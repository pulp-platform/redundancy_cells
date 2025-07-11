// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Michael Rogenmoser <michaero@iis.ee.ethz.ch>

`include "redundancy_cells/voters.svh"

module rel_fifo #(
  /// fifo is in fall-through mode
  parameter bit          FallThrough = 1'b0,
  /// default data width if the fifo is of type logic
  parameter int unsigned DataWidth   = 32,
  /// depth can be arbitrary from 0 to 2**32
  parameter int unsigned Depth       = 8,
  /// custom data type, overrides DataWidth parameter
  parameter type         data_t      = logic [DataWidth-1:0],
  /// Status and control signals are triplicated
  parameter bit          TmrStatus   = 1'b0,
  /// Input data has ECC (setting to 0 will add ecc encoders and decoders and assume simple logic vector, currently unimplemented)
  parameter bit          DataHasEcc  = 1'b1,
  /// Use dedicated registers for status_cnt_q (better timing, higher area, likely to be optimized away, currently unimplemented)
  parameter bit          StatusFF    = 1'b0,
  /// Have the TMR before the register, otherwise after.
  parameter bit          TmrBeforeReg = 1'b1,
  // DO NOT OVERWRITE THESE PARAMETERS
  parameter int unsigned AddrDepth   = cf_math_pkg::idx_width(Depth),
  parameter int unsigned HsWidth     = TmrStatus ? 3 : 1
)(
  /// Clock
  input  logic                 clk_i,
  /// Asynchronous reset active low
  input  logic                 rst_ni,
  /// flush the queue
  input  logic [  HsWidth-1:0] flush_i,
  /// test_mode to bypass clock gating
  input  logic                 testmode_i,
  /// status flags:
  /// queue is full
  output logic [  HsWidth-1:0] full_o,
  /// queue is empty
  output logic [  HsWidth-1:0] empty_o,
  /// fill pointer (unprotected, use full_o or empty_o)
  output logic [AddrDepth-1:0] usage_o,
  /// as long as the queue is not full we can push new data
  /// data to push into the queue
  input  data_t                data_i,
  /// data is valid and can be pushed to the queue
  input  logic [  HsWidth-1:0] push_i,
  /// as long as the queue is not empty we can pop new elements
  /// output data
  output data_t                data_o,
  /// pop head from queue
  input  logic [  HsWidth-1:0] pop_i,
  /// tmr fault output signal
  output logic                 fault_o
);
  // local parameter
  // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
  localparam int unsigned FifoDepth = (Depth > 0) ? Depth : 1;

  // TODO: DataHasEcc ? data_t : logic [hsiao_pkg::min_ecc(DataWidth)+DataWidth-1:0];
  localparam type ecc_data_t = data_t;

  logic [5:0] tmr_faults;
  logic [FifoDepth-1:0][$bits(ecc_data_t)-1:0] data_tmr_faults;
  assign fault_o = |tmr_faults;

  // clock gating control
  logic [FifoDepth-1:0][2:0] gate_clock;
  // pointer to the read and write section of the queue
  logic [2:0][AddrDepth:0] read_pointer_n,
                           read_pointer_q,
                           write_pointer_n,
                           write_pointer_q,
                           status_cnt_n,
                           status_cnt_q;
  logic [2:0] full, empty;

  ecc_data_t data_in;
  ecc_data_t [2:0] data_out;

  // actual memory
  ecc_data_t [FifoDepth-1:0] mem_q;

  if (!DataHasEcc) begin : gen_ecc_encode
    $error("unimplemented");
    // TODO ecc encoding of data_i into data_in
    // TODO ecc decoding of data_out into data_o
  end else begin : gen_ecc_passthrough
    assign data_in = data_i;
    `VOTE31F(data_out, data_o, tmr_faults[0])
  end

  if (StatusFF) begin : gen_status_ff
    $error("unimplemented");
    // logic [2:0][AddrDepth:0] status_cnt_d;

    // always_comb begin
    //   if ()
    // end

    // always_ff @(posedge clk_i or negedge rst_ni) begin : proc_status_cnt
    //   if(!rst_ni) begin
    //     status_cnt_q <= '0;
    //   end else begin
    //     status_cnt_q <= status_cnt_d;
    //   end
    // end
  end else begin : gen_status_calc
    for (genvar i = 0; i < 3; i++) begin : gen_tmr_status
      assign status_cnt_q[i] = write_pointer_q[i] - read_pointer_q[i];
    end
  end

  assign usage_o = status_cnt_q[0][AddrDepth-1:0];

  // status flags
  if (Depth == 0) begin : gen_pass_through
    assign empty_o     = ~push_i;
    assign full_o      = ~pop_i;
  end else begin : gen_fifo
    for (genvar i = 0; i < 3; i++) begin : gen_tmr_full_empty
      if (StatusFF) begin : gen_full_empty_from_status
        assign full[i]  = (status_cnt_q[i] == FifoDepth[AddrDepth:0]);
        assign empty[i] = (status_cnt_q[i] == 0) & ~(FallThrough & push_i[i]);
      end else begin : gen_full_empty_calc
        assign full[i]  = (write_pointer_q[i][AddrDepth-1:0] == read_pointer_q[i][AddrDepth-1:0] &
                           write_pointer_q[i][AddrDepth]     != read_pointer_q[i][AddrDepth]);
        assign empty[i] = (write_pointer_q[i]                == read_pointer_q[i]) &
                           ~(FallThrough & push_i[i]);
      end
    end
    if (TmrStatus) begin : gen_tmr_status
      assign full_o = full;
      assign empty_o = empty;
      assign tmr_faults[1] = '0;
      assign tmr_faults[2] = '0;
    end else begin : gen_voted_status
      TMR_voter_fail #(
        .VoterType(1)
      ) i_full_tmr_vote (
        .a_i(full[0]),
        .b_i(full[1]),
        .c_i(full[2]),
        .majority_o(full_o),
        .fault_detected_o(tmr_faults[1])
      );
      TMR_voter_fail #(
        .VoterType(1)
      ) i_empty_tmr_vote (
        .a_i(empty[0]),
        .b_i(empty[1]),
        .c_i(empty[2]),
        .majority_o(empty_o),
        .fault_detected_o(tmr_faults[2])
      );
    end

  end

  // read and write queue logic
  always_comb begin : read_write_comb
    // default assignment
    read_pointer_n  = read_pointer_q;
    write_pointer_n = write_pointer_q;
    status_cnt_n    = status_cnt_q;
    data_out [0]    = (Depth == 0) ? data_in : mem_q[read_pointer_q[0][AddrDepth-1:0]];
    data_out [1]    = (Depth == 0) ? data_in : mem_q[read_pointer_q[1][AddrDepth-1:0]];
    data_out [2]    = (Depth == 0) ? data_in : mem_q[read_pointer_q[2][AddrDepth-1:0]];
    gate_clock      = {FifoDepth{3'b111}};

    // For reliability we vote at the end and handle streams individually
    for (int i = 0; i < 3; i++) begin

      // For reliability each data bit handled individually
      for (int j = 0; j < $bits(ecc_data_t); j++) begin

        // push a new element to the queue
        if (push_i[i] && ~full[i]) begin
          // un-gate the clock, we want to write something
          gate_clock[write_pointer_q[i][AddrDepth-1:0]][i] = 1'b0;
          // increment the write counter
          // this is dead code when DEPTH is a power of two
          if (write_pointer_q[i][AddrDepth-1:0] == FifoDepth[AddrDepth-1:0] - 1) begin
              write_pointer_n[i][AddrDepth-1:0] = '0;
              write_pointer_n[i][AddrDepth] = ~write_pointer_q[i][AddrDepth];
          end else begin
              write_pointer_n[i] = write_pointer_q[i] + 1;
          end
          if (StatusFF) begin
            // increment the overall counter
            status_cnt_n[i]    = status_cnt_q[i] + 1;
          end
        end

        // pop an element from the queue
        if (pop_i[i] && ~empty[i]) begin
          // read from the queue is a default assignment
          // but increment the read pointer...
          // this is dead code when DEPTH is a power of two
          if (read_pointer_q[i][AddrDepth-1:0] == FifoDepth[AddrDepth-1:0] - 1) begin
              read_pointer_n[i][AddrDepth-1:0] = '0;
              read_pointer_n[i][AddrDepth] = ~read_pointer_q[i][AddrDepth];
          end else begin
              read_pointer_n[i] = read_pointer_q[i] + 1;
          end
          // ... and decrement the overall count
          if (StatusFF) begin
            status_cnt_n[i]   = status_cnt_q[i] - 1;
          end
        end

        // keep the count pointer stable if we push and pop at the same time
        if (StatusFF) begin
          if (push_i[i] && pop_i[i] &&  ~full[i] && ~empty[i])
            status_cnt_n   = status_cnt_q;
        end

        // FIFO is in pass through mode -> do not change the pointers
        if (FallThrough && (write_pointer_q[i] == read_pointer_q[i]) && push_i[i]) begin
          data_out[i] = data_in;
          if (pop_i[i]) begin
            status_cnt_n[i] = status_cnt_q[i];
            read_pointer_n[i] = read_pointer_q[i];
            write_pointer_n[i] = write_pointer_q[i];
          end
        end
      end
    end
  end

  if (TmrBeforeReg) begin : gen_tmr_before_reg
    logic [2:0][AddrDepth:0] read_pointer_voted, write_pointer_voted;

    `VOTE33F(read_pointer_n, read_pointer_voted, tmr_faults[4])
    `VOTE33F(write_pointer_n, write_pointer_voted, tmr_faults[5])

    for (genvar i = 0; i < 3; i++) begin : gen_pointer_ffs
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
          read_pointer_q[i]  <= '0;
          write_pointer_q[i] <= '0;
        end else begin
          if (flush_i[i]) begin
            read_pointer_q[i] <= '0;
            write_pointer_q[i] <= '0;
          end else begin
            read_pointer_q[i]  <= read_pointer_voted[i];
            write_pointer_q[i] <= write_pointer_voted[i];
          end
        end
      end
    end
  end else begin : gen_tmr_after_reg
    logic [2:0][AddrDepth:0] read_pointer_next, write_pointer_next;

    `VOTE33F(read_pointer_next,  read_pointer_q, tmr_faults[4])
    `VOTE33F(write_pointer_next, write_pointer_q, tmr_faults[5])

    for (genvar i = 0; i < 3; i++) begin : gen_pointer_ffs
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
          read_pointer_next[i]  <= '0;
          write_pointer_next[i] <= '0;
        end else begin
          if (flush_i) begin
            read_pointer_next[i]  <= '0;
            write_pointer_next[i] <= '0;
          end else begin
            read_pointer_next[i]  <= read_pointer_n[i];
            write_pointer_next[i] <= write_pointer_n[i];
          end
        end
      end
    end
  end

  assign tmr_faults[3] = |data_tmr_faults;

  for (genvar i = 0; i < FifoDepth; i++) begin : gen_mem_ffs_depth
    for (genvar j = 0; j < $bits(ecc_data_t); j++) begin : gen_mem_ffs
      logic gate_clock_local;
      `VOTE31F(gate_clock[i], gate_clock_local, data_tmr_faults[i][j])
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
          mem_q[i][j] <= '0;
        end else if (!gate_clock_local) begin
          mem_q[i][j] <= data_in[j];
        end
      end
    end
  end

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (Depth > 0)             else $error("Depth must be greater than 0.");
  end

  full_write : assert property(
    @(posedge clk_i) disable iff (~rst_ni) (full_o |-> ~push_i))
    else $fatal (1, "Trying to push new data although the FIFO is full.");

  empty_read : assert property(
    @(posedge clk_i) disable iff (~rst_ni) (empty_o |-> ~pop_i))
    else $fatal (1, "Trying to pop data although the FIFO is empty.");
`endif
// pragma translate_on

endmodule
