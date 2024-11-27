// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>, ETH Zurich
//         Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 10.04.2023
// Description: logarithmic arbitration tree with round robin arbitration scheme
// that can be externally locked to not arbitrate and just send the same output.

/// The rr_arb_tree employs non-starving round robin-arbitration - i.e., the priorities
/// rotate each cycle.
///
/// ## Fair vs. unfair Arbitration
///
/// This refers to fair throughput distribution when not all inputs have active requests.
/// This module has an internal state `rr_q` which defines the highest priority input. (When
/// `ExtPrio` is `1'b1` this state is provided from the outside.) The arbitration tree will
/// choose the input with the same index as currently defined by the state if it has an active
/// request. Otherwise a *random* other active input is selected. The parameter `FairArb` is used
/// to distinguish between two methods of calculating the next state.
/// * `1'b0`: The next state is calculated by advancing the current state by one. This leads to the
///           state being calculated without the context of the active request. Leading to an
///           unfair throughput distribution if not all inputs have active requests.
/// * `1'b1`: The next state jumps to the next unserved request with higher index.
///           This is achieved by using two trailing-zero-counters (`lzc`). The upper has the masked
///           `req_i` signal with all indices which will have a higher priority in the next state.
///           The trailing zero count defines the input index with the next highest priority after
///           the current one is served. When the upper is empty the lower `lzc` provides the
///           wrapped index if there are outstanding requests with lower or same priority.
/// The implication of throughput fairness on the module timing are:
/// * The trailing zero counter (`lzc`) has a loglog relation of input to output timing. This means
///   that in this module the input to register path scales with Log(Log(`NumIn`)).
/// * The `rr_arb_tree` data multiplexing scales with Log(`NumIn`). This means that the input to output
///   timing path of this module also scales scales with Log(`NumIn`).
/// This implies that in this module the input to output path is always longer than the input to
/// register path. As the output data usually also terminates in a register the parameter `FairArb`
/// only has implications on the area. When it is `1'b0` a static plus one adder is instantiated.
/// If it is `1'b1` two `lzc`, a masking logic stage and a two input multiplexer are instantiated.
/// However these are small in respect of the data multiplexers needed, as the width of the `req_i`
/// signal is usually less as than `DataWidth`.

`include "redundancy_cells/voters.svh"

module rr_arb_tree_lock #(
  /// Number of inputs to be arbitrated.
  parameter int unsigned NumIn      = 64,
  /// Data width of the payload in bits. Not needed if `DataType` is overwritten.
  parameter int unsigned DataWidth  = 32,
  /// Data type of the payload, can be overwritten with custom type. Only use of `DataWidth`.
  parameter type         DataType   = logic [DataWidth-1:0],
  /// The `ExtPrio` option allows to override the internal round robin counter via the
  /// `rr_i` signal. This can be useful in case multiple arbiters need to have
  /// rotating priorities that are operating in lock-step. If static priority arbitration
  /// is needed, just connect `rr_i` to '0.
  ///
  /// Set to 1'b1 to enable.
  parameter bit          ExtPrio    = 1'b0,
  /// If `AxiVldRdy` is set, the req/gnt signals are compliant with the AXI style vld/rdy
  /// handshake. Namely, upstream vld (req) must not depend on rdy (gnt), as it can be deasserted
  /// again even though vld is asserted. Enabling `AxiVldRdy` leads to a reduction of arbiter
  /// delay and area.
  ///
  /// Set to `1'b1` to treat req/gnt as vld/rdy.
  parameter bit          AxiVldRdy  = 1'b0,
  /// When set, ensures that throughput gets distributed evenly between all inputs.
  ///
  /// Set to `1'b0` to disable.
  parameter bit          FairArb    = 1'b1,
  /// Dependent parameter, do **not** overwrite.
  /// Width of the arbitration priority signal and the arbitrated index.
  parameter int unsigned IdxWidth   = (NumIn > 32'd1) ? unsigned'($clog2(NumIn)) : 32'd1,
  /// Dependent parameter, do **not** overwrite.
  /// Type for defining the arbitration priority and arbitrated index signal.
  parameter type         idx_t      = logic [IdxWidth-1:0],
  // Determines if the internal state machines should
  // be parallely redundant, meaning errors inside this module
  // can also not cause errors in the output
  // The external output is never protected!
  parameter bit          InternalRedundancy = 0,
  // Do not modify
  localparam int         REP        = InternalRedundancy ? 3 : 1
) (
  /// Clock, positive edge triggered.
  input  logic                clk_i,
  /// Asynchronous reset, active low.
  input  logic                rst_ni,
  /// Clears the arbiter state. Only used if `ExtPrio` is `1'b0` or `LockIn` is `1'b1`.
  input  logic      [REP-1:0] flush_i,
  /// External round-robin priority.
  input  idx_t                rr_i,
  /// lock idx signal, only used if `ExtPrio` is `1'b0.`
  input logic       [REP-1:0] lock_rr_i,
  /// Input requests arbitration.
  input  logic    [NumIn-1:0] req_i,
  /* verilator lint_off UNOPTFLAT */
  /// Input request is granted.
  output logic    [NumIn-1:0] gnt_o,
  /* verilator lint_on UNOPTFLAT */
  /// Input data for arbitration.
  input  DataType [NumIn-1:0] data_i,
  /// Output request is valid.
  output logic                req_o,
  /// Output request is granted.
  input  logic                gnt_i,
  /// Output data.
  output DataType             data_o,
  /// Index from which input the data came from.
  output idx_t                idx_o
);

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef XSIM
  // Default SVA reset
  default disable iff (!rst_ni || flush_i[0]);
  `endif
  `endif
  // pragma translate_on

  // just pass through in this corner case
  if (NumIn == unsigned'(1)) begin : gen_pass_through
    assign req_o    = req_i[0];
    assign gnt_o[0] = gnt_i;
    assign data_o   = data_i[0];
    assign idx_o    = '0;
  // non-degenerate cases
  end else begin : gen_arbiter
    localparam int unsigned NumLevels = unsigned'($clog2(NumIn));

    /* verilator lint_off UNOPTFLAT */
    idx_t    [2**NumLevels-2:0][REP-1:0] index_nodes; // used to propagate the indices
    DataType [2**NumLevels-2:0] data_nodes;  // used to propagate the data
    logic    [2**NumLevels-2:0] gnt_nodes;   // used to propagate the grant to masters
    logic    [2**NumLevels-2:0] req_nodes;   // used to propagate the requests to slave
    /* lint_off */
    idx_t [REP-1:0]             rr_q;
    logic [NumIn-1:0]           req_d;

    // the final arbitration decision can be taken from the root of the tree
    assign req_o        = req_nodes[0];
    assign data_o       = data_nodes[0];
    assign idx_o        = index_nodes[0][0];


    if (ExtPrio) begin : gen_ext_rr
      assign rr_q[0]    = rr_i;
      assign req_d      = req_i;
    end else begin : gen_int_rr
      idx_t [REP-1:0] rr_d;

      assign req_d = req_i;

      idx_t next_idx;

      if (FairArb) begin : gen_fair_arb

        logic [NumIn-1:0] upper_mask,  lower_mask;
        idx_t             upper_idx,   lower_idx;
        logic             upper_empty, lower_empty;

        for (genvar i = 0; i < NumIn; i++) begin : gen_mask
          assign upper_mask[i] = (i >  rr_q[0]) ? req_d[i] : 1'b0;
          assign lower_mask[i] = (i <= rr_q[0]) ? req_d[i] : 1'b0;
        end

        lzc #(
          .WIDTH ( NumIn ),
          .MODE  ( 1'b0  )
        ) i_lzc_upper (
          .in_i    ( upper_mask  ),
          .cnt_o   ( upper_idx   ),
          .empty_o ( upper_empty )
        );

        lzc #(
          .WIDTH ( NumIn ),
          .MODE  ( 1'b0  )
        ) i_lzc_lower (
          .in_i    ( lower_mask  ),
          .cnt_o   ( lower_idx   ),
          .empty_o ( /*unused*/  )
        );

        assign next_idx = upper_empty      ? lower_idx : upper_idx;
      end else begin : gen_unfair_arb
        assign next_idx = ((rr_q[0] == idx_t'(NumIn-1)) ? '0 : rr_q[0] + 1'b1);
      end

      idx_t [REP-1:0] voted_idx, voted_rr_q;
      `VOTEXX(REP, index_nodes[0], voted_idx);
      `VOTEXX(REP, rr_q, voted_rr_q);

      for (genvar r = 0; r < REP; r++) begin: gen_rr
        always_comb begin
          if (lock_rr_i[r]) begin
            rr_d[r] = voted_idx[r];
          end else begin
            if (gnt_i && req_o) begin
              rr_d[r] = next_idx;
            end else begin
                rr_d[r] = voted_rr_q[r];
            end
          end
        end

        // this holds the highest priority
        always_ff @(posedge clk_i or negedge rst_ni) begin : p_rr_regs
          if (!rst_ni) begin
            rr_q[r]   <= '0;
          end else begin
            if (flush_i[r]) begin
              rr_q[r]   <= '0;
            end else begin
              rr_q[r]   <= rr_d[r];
            end
          end
        end
      end
    end

    logic [REP-1:0] lock_rr_q;
    for (genvar r = 0; r < REP; r++) begin: gen_lock_q
      always_ff @(posedge clk_i or negedge rst_ni) begin : p_lock_reg
        if (!rst_ni) begin
          lock_rr_q[r]   <= '1;
        end else begin
          if (flush_i[r]) begin
            lock_rr_q[r]   <= '0;
          end else begin
            lock_rr_q[r]   <= lock_rr_i[r];
          end
        end
      end
    end

    assign gnt_nodes[0] = gnt_i;

    // arbiter tree
    for (genvar level = 0; unsigned'(level) < NumLevels; level++) begin : gen_levels
      for (genvar l = 0; l < 2**level; l++) begin : gen_level
        // local select signal
        logic [REP-1:0] sel;
        // index calcs
        localparam int unsigned Idx0 = 2**level-1+l;// current node
        localparam int unsigned Idx1 = 2**(level+1)-1+l*2;
        //////////////////////////////////////////////////////////////
        // uppermost level where data is fed in from the inputs
        if (unsigned'(level) == NumLevels-1) begin : gen_first_level
          // if two successive indices are still in the vector...
          if (unsigned'(l) * 2 < NumIn-1) begin : gen_reduce

            for (genvar r = 0; r < REP; r++) begin: gen_select
              // arbitration: round robin
              always_comb begin
                if (lock_rr_q[r]) begin
                  sel[r] = rr_q[r][NumLevels-1-level];
                end else begin
                  sel[r] =  ~req_d[l*2] | req_d[l*2+1] & rr_q[0][NumLevels-1-level];
                end
              end
              assign index_nodes[Idx0][r] = idx_t'(sel[r]);
            end

            assign req_nodes[Idx0]   = (sel[0]) ? req_d[l*2+1] : req_d[l*2] ;
            assign data_nodes[Idx0]  = (sel[0]) ? data_i[l*2+1] : data_i[l*2];
            assign gnt_o[l*2]        = gnt_nodes[Idx0] & (AxiVldRdy | req_d[l*2])   & ~sel[0];
            assign gnt_o[l*2+1]      = gnt_nodes[Idx0] & (AxiVldRdy | req_d[l*2+1]) & sel[0];
          end
          // if only the first index is still in the vector...
          if (unsigned'(l) * 2 == NumIn-1) begin : gen_first
            assign req_nodes[Idx0]   = req_d[l*2];
            assign index_nodes[Idx0] = '0;
            assign data_nodes[Idx0]  = data_i[l*2];
            assign gnt_o[l*2]        = gnt_nodes[Idx0] & (AxiVldRdy | req_d[l*2]);
          end
          // if index is out of range, fill up with zeros (will get pruned)
          if (unsigned'(l) * 2 > NumIn-1) begin : gen_out_of_range
            assign req_nodes[Idx0]   = 1'b0;
            assign index_nodes[Idx0] = '0;
            assign data_nodes[Idx0]  = DataType'('0);
          end
        //////////////////////////////////////////////////////////////
        // general case for other levels within the tree
        end else begin : gen_other_levels

          // arbitration: round robin
          for (genvar r = 0; r < REP; r++) begin: gen_select
            always_comb begin
              if (lock_rr_q[r]) begin
                sel[r] = rr_q[r][NumLevels-1-level];
              end else begin
                sel[r] =  ~req_nodes[Idx1] | req_nodes[Idx1+1] & rr_q[0][NumLevels-1-level];
              end
            end

            assign index_nodes[Idx0][r] = (sel[r]) ?
              idx_t'({1'b1, index_nodes[Idx1+1][r][NumLevels-unsigned'(level)-2:0]}) :
              idx_t'({1'b0, index_nodes[Idx1][r][NumLevels-unsigned'(level)-2:0]});
          end

          assign req_nodes[Idx0]   = (sel[0]) ? req_nodes[Idx1+1]  : req_nodes[Idx1];
          assign data_nodes[Idx0]  = (sel[0]) ? data_nodes[Idx1+1] : data_nodes[Idx1];
          assign gnt_nodes[Idx1]   = gnt_nodes[Idx0] & ~sel[0];
          assign gnt_nodes[Idx1+1] = gnt_nodes[Idx0] & sel[0];
        end
        //////////////////////////////////////////////////////////////
      end
    end

    // pragma translate_off
    `ifndef VERILATOR
    `ifndef XSIM
    initial begin : p_assert
      assert(NumIn)
        else $error(1, "Input must be at least one element wide.");
      assert(!(ExtPrio && (REP > 1)))
        else $error(1, "There is no reason to use REP > 1 with ExtPrio!");
    end

    hot_one : assert property(
      @(posedge clk_i) $onehot0(gnt_o))
        else $error (1, "Grant signal must be hot1 or zero.");

    gnt0 : assert property(
      @(posedge clk_i) |gnt_o |-> gnt_i)
        else $error (1, "Grant out implies grant in.");

    gnt1 : assert property(
      @(posedge clk_i) req_o |-> gnt_i |-> |gnt_o)
        else $error (1, "Req out and grant in implies grant out.");

    gnt_idx : assert property(
      @(posedge clk_i) req_o |->  gnt_i |-> gnt_o[idx_o])
        else $error (1, "Idx_o / gnt_o do not match.");

    req1 : assert property(
      @(posedge clk_i) req_o |-> |req_i)
        else $error (1, "Req out implies req in.");

    lock2 : assert property(
      @(posedge clk_i) disable iff (!rst_ni) lock_rr_q[0] |-> idx_o == $past(idx_o))
        else $error (1, "Lock means idx_o does not change.");
    `endif
    `endif
    // pragma translate_on
  end

endmodule : rr_arb_tree_lock
