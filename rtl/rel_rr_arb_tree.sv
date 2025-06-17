// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Rogenmoser <michaero@iis.ee.ethz.ch

// Description: fault-tolerant logarithmic arbitration tree with round robin arbitration scheme.

`include "redundancy_cells/voters.svh"

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

/// TODO: unfair arb or external priority may not be reliable!
module rel_rr_arb_tree #(
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
  /// The `LockIn` option prevents the arbiter from changing the arbitration
  /// decision when the arbiter is disabled. I.e., the index of the first request
  /// that wins the arbitration will be locked in case the destination is not
  /// able to grant the request in the same cycle.
  ///
  /// Set to `1'b1` to enable.
  parameter bit          LockIn     = 1'b0,
  /// When set, ensures that throughput gets distributed evenly between all inputs.
  ///
  /// Set to `1'b0` to disable.
  parameter bit          FairArb    = 1'b1,
  /// IO handshake signal triplicated or not
  parameter bit          TmrStatus  = 1'b0,
  /// Have the TMR before the register, otherwise after.
  parameter bit          TmrBeforeReg = 1'b1,
  /// Dependent parameter, do **not** overwrite.
  /// Width of the arbitration priority signal and the arbitrated index.
  parameter int unsigned IdxWidth   = (NumIn > 32'd1) ? unsigned'($clog2(NumIn)) : 32'd1,
  /// Dependent parameter, do **not** overwrite.
  /// Type for defining the arbitration priority and arbitrated index signal.
  parameter type         idx_t      = logic [IdxWidth-1:0],
  /// Dependent parameter, do **not** overwrite.
  parameter int unsigned HsWidth    = TmrStatus ? 3 : 1
) (
  /// Clock, positive edge triggered.
  input  logic                clk_i,
  /// Asynchronous reset, active low.
  input  logic                rst_ni,
  /// Clears the arbiter state. Only used if `ExtPrio` is `1'b0` or `LockIn` is `1'b1`.
  input  logic                flush_i,
  /// External round-robin priority. Only used if `ExtPrio` is `1'b1.`
  input  idx_t                rr_i,
  /// Input requests arbitration.
  input  logic    [NumIn-1:0][HsWidth-1:0] req_i,
  /* verilator lint_off UNOPTFLAT */
  /// Input request is granted.
  output logic    [NumIn-1:0][HsWidth-1:0] gnt_o,
  /* verilator lint_on UNOPTFLAT */
  /// Input data for arbitration.
  input  DataType [NumIn-1:0] data_i,
  /// Output request is valid.
  output logic               [HsWidth-1:0] req_o,
  /// Output request is granted.
  input  logic               [HsWidth-1:0] gnt_i,
  /// Output data.
  output DataType             data_o,
  /// Index from which input the data came from.
  output idx_t               [HsWidth-1:0] idx_o,
  /// Reliability error
  output logic                             fault_o
);

  `ifndef SYNTHESIS
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ifndef VERILATOR
  `ifndef XSIM
  // Default SVA reset
  default disable iff (!rst_ni || flush_i);
  `endif
  `endif
  `endif
  `endif

  logic [8+NumIn-1:0] tmr_errors;
  assign fault_o = |tmr_errors;

  // just pass through in this corner case
  if (NumIn == unsigned'(1)) begin : gen_pass_through
    assign req_o    = req_i[0];
    assign gnt_o[0] = gnt_i;
    assign data_o   = data_i[0];
    assign idx_o    = '0;
    assign tmr_errors = '0;
  // non-degenerate cases
  end else begin : gen_arbiter
    logic [NumIn-1:0][2:0] req_in, gnt_out;
    logic            [2:0] req_out, gnt_in;
    idx_t            [2:0] idx_out;
    if (TmrStatus) begin : gen_req_in
      assign req_in = req_i;
      assign req_o = req_out;
      assign gnt_o = gnt_out;
      assign gnt_in = gnt_i;
      assign idx_o = idx_out;
      assign tmr_errors[4:0] = '0;
    end else begin : gen_req_in_triplicate
      for (genvar i = 0; i < NumIn; i++) begin : gen_req_in
        assign req_in[i] = {3{req_i[i]}};
        TMR_voter_fail #(
          .VoterType(1)
        ) i_gnt_o_vote (
          .a_i(gnt_out[i][0]),
          .b_i(gnt_out[i][1]),
          .c_i(gnt_out[i][2]),
          .majority_o(gnt_o[i]),
          .fault_detected_o(tmr_errors[i])
        );
      end
        TMR_voter_fail #(
          .VoterType(1)
        ) i_req_o_vote (
          .a_i(req_out[0]),
          .b_i(req_out[1]),
          .c_i(req_out[2]),
          .majority_o(req_o),
          .fault_detected_o(tmr_errors[3])
        );
      assign gnt_in = gnt_i;
        TMR_voter_fail #(
          .VoterType(1)
        ) i_idx_o_vote (
          .a_i(idx_out[0]),
          .b_i(idx_out[1]),
          .c_i(idx_out[2]),
          .majority_o(idx_o),
          .fault_detected_o(tmr_errors[4])
        );
    end

    localparam int unsigned NumLevels = unsigned'($clog2(NumIn));

    /* verilator lint_off UNOPTFLAT */
    idx_t    [2**NumLevels-2:0][2:0] index_nodes; // used to propagate the indices
    DataType [2**NumLevels-2:0][2:0] data_nodes;  // used to propagate the data
    logic    [2**NumLevels-2:0][2:0] gnt_nodes;   // used to propagate the grant to masters
    logic    [2**NumLevels-2:0][2:0] req_nodes;   // used to propagate the requests to slave
    /* lint_off */
    idx_t            [2:0]      rr_q;
    logic [NumIn-1:0][2:0]      req_d;

    // the final arbitration decision can be taken from the root of the tree
    assign req_out        = req_nodes[0];
    assign idx_out        = index_nodes[0];
    // assign data_o       = data_nodes[0];
    bitwise_TMR_voter_fail #(
      .DataWidth($bits(DataType)),
      .VoterType(1)
    ) i_data_vote (
      .a_i        (data_nodes[0][0]),
      .b_i        (data_nodes[0][1]),
      .c_i        (data_nodes[0][2]),
      .majority_o (data_o),
      .fault_detected_o(tmr_errors[5])
    );

    if (ExtPrio) begin : gen_ext_rr
      assign rr_q       = {3{rr_i}};
      assign req_d      = req_in;
    end else begin : gen_int_rr
      idx_t [2:0] rr_d;

      // lock arbiter decision in case we got at least one req and no acknowledge
      if (LockIn) begin : gen_lock
        logic [2:0] lock_d, lock_q;
        logic [NumIn-1:0][2:0] req_q;

        assign lock_d     = req_out & ~gnt_in;
        for (genvar i = 0; i < NumIn; i++) begin : gen_req_d
          for (genvar j = 0; j < 3; j++) begin : gen_req_d_tmr
            assign req_d[i][j] = (lock_q[j]) ? req_q[i][j] : req_in[i][j];
          end
        end

        if (TmrBeforeReg) begin : gen_lock_tmr_before_reg
          logic [2:0] lock_voted;
          TMR_voter_fail #(
            .VoterType(1)
          ) i_lock0_vote (
            .a_i(lock_d[0]),
            .b_i(lock_d[1]),
            .c_i(lock_d[2]),
            .majority_o(lock_voted[0]),
            .fault_detected_o(tmr_errors[6])
          );
          TMR_voter_fail #(
            .VoterType(1)
          ) i_lock1_vote (
            .a_i(lock_d[0]),
            .b_i(lock_d[1]),
            .c_i(lock_d[2]),
            .majority_o(lock_voted[1]),
            .fault_detected_o()
          );
          TMR_voter_fail #(
            .VoterType(1)
          ) i_lock2_vote (
            .a_i(lock_d[0]),
            .b_i(lock_d[1]),
            .c_i(lock_d[2]),
            .majority_o(lock_voted[2]),
            .fault_detected_o()
          );
          always_ff @(posedge clk_i or negedge rst_ni) begin : p_lock_reg
            if (!rst_ni) begin
              lock_q <= '0;
            end else begin
              if (flush_i) begin
                lock_q <= '0;
              end else begin
                lock_q <= lock_voted;
              end
            end
          end
        end else begin : gen_lock_tmr_after_reg
          logic [2:0] lock_next;
          TMR_voter_fail #(
            .VoterType(1)
          ) i_lock0_vote (
            .a_i(lock_next[0]),
            .b_i(lock_next[1]),
            .c_i(lock_next[2]),
            .majority_o(lock_q[0]),
            .fault_detected_o(tmr_errors[6])
          );
          TMR_voter_fail #(
            .VoterType(1)
          ) i_lock1_vote (
            .a_i(lock_next[0]),
            .b_i(lock_next[1]),
            .c_i(lock_next[2]),
            .majority_o(lock_q[1]),
            .fault_detected_o()
          );
          TMR_voter_fail #(
            .VoterType(1)
          ) i_lock2_vote (
            .a_i(lock_next[0]),
            .b_i(lock_next[1]),
            .c_i(lock_next[2]),
            .majority_o(lock_q[2]),
            .fault_detected_o()
          );
          always_ff @(posedge clk_i or negedge rst_ni) begin : p_lock_reg
            if (!rst_ni) begin
              lock_next <= '0;
            end else begin
              if (flush_i) begin
                lock_next <= '0;
              end else begin
                lock_next <= lock_d;
              end
            end
          end
        end


        `ifndef SYNTHESIS
        `ifndef COMMON_CELLS_ASSERTS_OFF
          lock: assert property(
            @(posedge clk_i) disable iff (!rst_ni || flush_i)
                LockIn |-> req_o[0] && (!gnt_i[0] && !flush_i) |=> idx_o[0] == $past(idx_o[0])) else
                $fatal (1, {"Lock implies same arbiter decision in next cycle if output is not ",
                            "ready."});

          logic [NumIn-1:0][2:0] req_tmp;
          assign req_tmp = req_q & req_in;
          lock_req: assume property(
            @(posedge clk_i) disable iff (!rst_ni || flush_i)
                LockIn |-> lock_d[0] |=> req_tmp == req_q) else
                $fatal (1, {"It is disallowed to deassert unserved request signals when LockIn is ",
                            "enabled."});
        `endif
        `endif

        if (TmrBeforeReg) begin : gen_req_tmr_before_reg
          logic [NumIn-1:0][2:0] req_voted;
          for (genvar i = 0; i < NumIn; i++) begin : gen_vote_req
            TMR_voter_fail #(
              .VoterType(1)
            ) i_req_d0_vote (
              .a_i(req_d[i][0]),
              .b_i(req_d[i][1]),
              .c_i(req_d[i][2]),
              .majority_o(req_voted[i][0]),
              .fault_detected_o(tmr_errors[8+i])
            );
            TMR_voter_fail #(
              .VoterType(1)
            ) i_req_d1_vote (
              .a_i(req_d[i][0]),
              .b_i(req_d[i][1]),
              .c_i(req_d[i][2]),
              .majority_o(req_voted[i][1]),
              .fault_detected_o()
            );
            TMR_voter_fail #(
              .VoterType(1)
            ) i_req_d2_vote (
              .a_i(req_d[i][0]),
              .b_i(req_d[i][1]),
              .c_i(req_d[i][2]),
              .majority_o(req_voted[i][2]),
              .fault_detected_o()
            );
          end
          always_ff @(posedge clk_i or negedge rst_ni) begin : p_lock_reg
            if (!rst_ni) begin
              req_q <= '0;
            end else begin
              if (flush_i) begin
                req_q <= '0;
              end else begin
                req_q <= req_voted;
              end
            end
          end
        end else begin : gen_req_tmr_after_reg
          logic [NumIn-1:0][2:0] req_next;
          for (genvar i = 0; i < NumIn; i++) begin : gen_vote_req
            TMR_voter_fail #(
              .VoterType(1)
            ) i_req_next0_vote (
              .a_i(req_next[i][0]),
              .b_i(req_next[i][1]),
              .c_i(req_next[i][2]),
              .majority_o(req_q[i][0]),
              .fault_detected_o(tmr_errors[8+i])
            );
            TMR_voter_fail #(
              .VoterType(1)
            ) i_req_next1_vote (
              .a_i(req_next[i][0]),
              .b_i(req_next[i][1]),
              .c_i(req_next[i][2]),
              .majority_o(req_q[i][1]),
              .fault_detected_o()
            );
            TMR_voter_fail #(
              .VoterType(1)
            ) i_req_next2_vote (
              .a_i(req_next[i][0]),
              .b_i(req_next[i][1]),
              .c_i(req_next[i][2]),
              .majority_o(req_q[i][2]),
              .fault_detected_o()
            );
          end
          always_ff @(posedge clk_i or negedge rst_ni) begin : p_lock_reg
            if (!rst_ni) begin
              req_next <= '0;
            end else begin
              if (flush_i) begin
                req_next <= '0;
              end else begin
                req_next <= req_d;
              end
            end
          end
        end
      end else begin : gen_no_lock
        assign req_d = req_in;
        assign tmr_errors[7:6] = '0;
      end

      if (FairArb) begin : gen_fair_arb
        for (genvar j = 0; j < 3; j++) begin : gen_tmr_fair_arb
          logic [NumIn-1:0] upper_mask,  lower_mask;
          idx_t             upper_idx,   lower_idx,   next_idx;
          logic             upper_empty, lower_empty;

          for (genvar i = 0; i < NumIn; i++) begin : gen_mask
            assign upper_mask[i] = (i >  rr_q[j]) ? req_d[i][j] : 1'b0;
            assign lower_mask[i] = (i <= rr_q[j]) ? req_d[i][j] : 1'b0;
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
          assign rr_d[j]     = (gnt_in[j] && req_out[j]) ? next_idx  : rr_q[j];
        end
      end else begin : gen_unfair_arb
        for (genvar j = 0; j < 3; j++) begin : gen_tmr_unfair_arb
          assign rr_d[j] = (gnt_in[j] && req_out[j]) ?
                           ((rr_q[j] == idx_t'(NumIn-1)) ? '0 : rr_q[j] + 1'b1) : rr_q[j];
        end
      end

      // this holds the highest priority
      if (TmrBeforeReg) begin : gen_rr_tmr_before_reg
        idx_t [2:0] rr_voted;
        bitwise_TMR_voter_fail #(
          .DataWidth(IdxWidth),
          .VoterType(1)
        ) i_rr_d0_vote (
          .a_i(rr_d[0]),
          .b_i(rr_d[1]),
          .c_i(rr_d[2]),
          .majority_o(rr_voted[0]),
          .fault_detected_o(tmr_errors[7])
        );
        bitwise_TMR_voter_fail #(
          .DataWidth(IdxWidth),
          .VoterType(1)
        ) i_rr_d1_vote (
          .a_i(rr_d[0]),
          .b_i(rr_d[1]),
          .c_i(rr_d[2]),
          .majority_o(rr_voted[1]),
          .fault_detected_o()
        );
        bitwise_TMR_voter_fail #(
          .DataWidth(IdxWidth),
          .VoterType(1)
        ) i_rr_d2_vote (
          .a_i(rr_d[0]),
          .b_i(rr_d[1]),
          .c_i(rr_d[2]),
          .majority_o(rr_voted[2]),
          .fault_detected_o()
        );
        always_ff @(posedge clk_i or negedge rst_ni) begin : p_rr_regs
          if (!rst_ni) begin
            rr_q   <= '0;
          end else begin
            if (flush_i) begin
              rr_q   <= '0;
            end else begin
              rr_q   <= rr_voted;
            end
          end
        end
      end else begin : gen_rr_tmr_after_reg
        logic [2:0] rr_next;
        TMR_voter_fail #(
          .VoterType(1)
        ) i_rr_next0_vote (
          .a_i(rr_next[0]),
          .b_i(rr_next[1]),
          .c_i(rr_next[2]),
          .majority_o(rr_q[0]),
          .fault_detected_o(tmr_errors[7])
        );
        TMR_voter_fail #(
          .VoterType(1)
        ) i_rr_next1_vote (
          .a_i(rr_next[0]),
          .b_i(rr_next[1]),
          .c_i(rr_next[2]),
          .majority_o(rr_q[1]),
          .fault_detected_o()
        );
        TMR_voter_fail #(
          .VoterType(1)
        ) i_rr_next2_vote (
          .a_i(rr_next[0]),
          .b_i(rr_next[1]),
          .c_i(rr_next[2]),
          .majority_o(rr_q[2]),
          .fault_detected_o()
        );
        always_ff @(posedge clk_i or negedge rst_ni) begin : p_rr_regs
          if (!rst_ni) begin
            rr_next <= '0;
          end else begin
            if (flush_i) begin
              rr_next <= '0;
            end else begin
              rr_next <= rr_d;
            end
          end
        end
      end
    end

    assign gnt_nodes[0] = gnt_in;

    // arbiter tree
    for (genvar i = 0; i < 3; i++) begin : gen_tmr_arb_tree
      for (genvar level = 0; unsigned'(level) < NumLevels; level++) begin : gen_levels
        for (genvar l = 0; l < 2**level; l++) begin : gen_level
          // local select signal
          logic sel;
          // index calcs
          localparam int unsigned Idx0 = 2**level-1+l;// current node
          localparam int unsigned Idx1 = 2**(level+1)-1+l*2;
          //////////////////////////////////////////////////////////////
          // uppermost level where data is fed in from the inputs
          if (unsigned'(level) == NumLevels-1) begin : gen_first_level
            // if two successive indices are still in the vector...
            if (unsigned'(l) * 2 < NumIn-1) begin : gen_reduce
              assign req_nodes[Idx0][i]   = req_d[l*2][i] | req_d[l*2+1][i];

              // arbitration: round robin
              assign sel =  ~req_d[l*2][i] | req_d[l*2+1][i] & rr_q[i][NumLevels-1-level];

              assign index_nodes[Idx0][i] = idx_t'(sel);
              assign data_nodes[Idx0][i]  = (sel) ? data_i[l*2+1] : data_i[l*2];
              assign gnt_out[l*2][i]   = gnt_nodes[Idx0][i] & (AxiVldRdy | req_d[l*2][i])  & ~sel;
              assign gnt_out[l*2+1][i] = gnt_nodes[Idx0][i] & (AxiVldRdy | req_d[l*2+1][i]) & sel;
            end
            // if only the first index is still in the vector...
            if (unsigned'(l) * 2 == NumIn-1) begin : gen_first
              assign req_nodes[Idx0][i]   = req_d[l*2][i];
              assign index_nodes[Idx0][i] = '0;// always zero in this case
              assign data_nodes[Idx0][i]  = data_i[l*2];
              assign gnt_out[l*2][i]      = gnt_nodes[Idx0][i] & (AxiVldRdy | req_d[l*2][i]);
            end
            // if index is out of range, fill up with zeros (will get pruned)
            if (unsigned'(l) * 2 > NumIn-1) begin : gen_out_of_range
              assign req_nodes[Idx0][i]   = 1'b0;
              assign index_nodes[Idx0][i] = idx_t'('0);
              assign data_nodes[Idx0][i]  = DataType'('0);
            end
          //////////////////////////////////////////////////////////////
          // general case for other levels within the tree
          end else begin : gen_other_levels
            assign req_nodes[Idx0][i]   = req_nodes[Idx1][i] | req_nodes[Idx1+1][i];

            // arbitration: round robin
            assign sel =  ~req_nodes[Idx1][i] | req_nodes[Idx1+1][i] & rr_q[i][NumLevels-1-level];

            assign index_nodes[Idx0][i] = (sel) ?
              idx_t'({1'b1, index_nodes[Idx1+1][i][NumLevels-unsigned'(level)-2:0]}) :
              idx_t'({1'b0, index_nodes[Idx1][i][NumLevels-unsigned'(level)-2:0]});

            assign data_nodes[Idx0][i]  = (sel) ? data_nodes[Idx1+1][i] : data_nodes[Idx1][i];
            assign gnt_nodes[Idx1][i]   = gnt_nodes[Idx0][i] & ~sel;
            assign gnt_nodes[Idx1+1][i] = gnt_nodes[Idx0][i] & sel;
          end
          //////////////////////////////////////////////////////////////
        end
      end
    end

    `ifndef SYNTHESIS
    `ifndef COMMON_CELLS_ASSERTS_OFF
    `ifndef XSIM
    initial begin : p_assert
      assert(NumIn)
        else $fatal(1, "Input must be at least one element wide.");
      assert(!(LockIn && ExtPrio))
        else $fatal(1,"Cannot use LockIn feature together with external ExtPrio.");
    end

    logic [2:0][NumIn-1:0] gnt_o_trsp;
    for (genvar i = 0; i < NumIn; i++) begin : gen_numin_trsps
      for (genvar j = 0; j < 3; j++) begin : gen_tmr_trsp
        assign gnt_o_trsp[j][i] = gnt_o[i][j];
      end
    end

    hot_one : assert property(
      @(posedge clk_i) disable iff (!rst_ni || flush_i) $onehot0(gnt_o_trsp[0]))
        else $fatal (1, "Grant signal must be hot1 or zero.");

    gnt0 : assert property(
      @(posedge clk_i) disable iff (!rst_ni || flush_i) |gnt_o_trsp[0] |-> gnt_i[0])
        else $fatal (1, "Grant out implies grant in.");

    gnt1 : assert property(
      @(posedge clk_i) disable iff (!rst_ni || flush_i) req_o[0] |-> gnt_i[0] |-> |gnt_o_trsp[0])
        else $fatal (1, "Req out and grant in implies grant out.");

    gnt_idx : assert property(
      @(posedge clk_i) disable iff (!rst_ni || flush_i) req_o[0] |->
                                                        gnt_i[0] |-> gnt_o[idx_o[0]][0])
        else $fatal (1, "Idx_o / gnt_o do not match.");

    req0 : assert property(
      @(posedge clk_i) disable iff (!rst_ni || flush_i) |req_i |-> req_o)
        else $fatal (1, "Req in implies req out.");

    req1 : assert property(
      @(posedge clk_i) disable iff (!rst_ni || flush_i) req_o |-> |req_i)
        else $fatal (1, "Req out implies req in.");
    `endif
    `endif
    `endif
  end

endmodule
