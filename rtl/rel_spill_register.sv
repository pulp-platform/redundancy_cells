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

module rel_spill_register #(
  parameter type T           = logic, // Assumed ECC protected
  parameter bit  Bypass      = 1'b0,   // make this spill register transparent
  parameter bit  TmrHandshake = 1'b1,    // use TMR handshake
  parameter int unsigned HsWidth = TmrHandshake ? 3 : 1 // width of the handshake signals
) (
  input  logic clk_i   ,
  input  logic rst_ni  ,
  input  logic [HsWidth-1:0] valid_i ,
  output logic [HsWidth-1:0] ready_o ,
  input  T     data_i  ,
  output logic [HsWidth-1:0] valid_o ,
  input  logic [HsWidth-1:0] ready_i ,
  output T     data_o,
  output logic fault_o
);

  if (Bypass) begin : gen_bypass
    assign valid_o = valid_i;
    assign ready_o = ready_i;
    assign data_o  = data_i;
    assign fault_o = 1'b0; // No fault in bypass mode
  end else begin : gen_spill_reg
    logic [2:0] faults;
    assign fault_o = |faults;

    // The A register.
    T a_data_d, a_data_q;
    T [2:0] a_data_d_tmr;
    logic [2:0] a_full_q;
    logic [2:0] a_fill, a_drain;

    for (genvar i = 0; i < 3; i++) begin : gen_a_data_tmr
      assign a_data_d_tmr[i] = a_fill[i] ? data_i : a_data_q;
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( $bits(T) ),
      .VoterType ( 1 ) // KP_MV
    ) i_a_data_tmr (
      .a_i              ( a_data_d_tmr[0] ),
      .b_i              ( a_data_d_tmr[1] ),
      .c_i              ( a_data_d_tmr[2] ),
      .majority_o       ( a_data_d        ),
      .fault_detected_o ( faults[0]       )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_data
      if (!rst_ni)
        a_data_q <= '0;
      else
        a_data_q <= a_data_d;
    end

    for (genvar i = 0; i < 3; i++) begin : gen_a_full_q
      always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_full
        if (!rst_ni)
          a_full_q[i] <= '0;
        else if (a_fill[i] || a_drain[i])
          a_full_q[i] <= a_fill[i];
      end
    end

    // The B register.
    T b_data_d, b_data_q;
    T [2:0] b_data_d_tmr;
    logic [2:0] b_full_q;
    logic [2:0] b_fill, b_drain;

    for (genvar i = 0; i < 3; i++) begin : gen_b_data_tmr
      assign b_data_d_tmr[i] = b_fill[i] ? a_data_q : b_data_q;
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( $bits(T) ),
      .VoterType ( 1 ) // KP_MV
    ) i_b_data_tmr (
      .a_i              ( b_data_d_tmr[0] ),
      .b_i              ( b_data_d_tmr[1] ),
      .c_i              ( b_data_d_tmr[2] ),
      .majority_o       ( b_data_d        ),
      .fault_detected_o ( faults[1]       )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_data
      if (!rst_ni)
        b_data_q <= '0;
      else
        b_data_q <= b_data_d;
    end

    for (genvar i = 0; i < 3; i++) begin : gen_b_full_q
      always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_full
        if (!rst_ni)
          b_full_q[i] <= '0;
        else if (b_fill[i] || b_drain[i])
          b_full_q[i] <= b_fill[i];
      end
    end

    T [2:0] data_o_tmr;

    for (genvar i = 0; i < 3; i++) begin : gen_fill_drain
      // Fill the A register when the A or B register is empty. Drain the A register
      // whenever it is full and being filled, or if a flush is requested.
      assign a_fill[i] = valid_i[i] && ready_o[i];
      assign a_drain[i] = (a_full_q[i] && !b_full_q[i]);

      // Fill the B register whenever the A register is drained, but the downstream
      // circuit is not ready. Drain the B register whenever it is full and the
      // downstream circuit is ready, or if a flush is requested.
      assign b_fill[i] = a_drain[i] && (!ready_i[i]);
      assign b_drain[i] = (b_full_q[i] && ready_i[i]);

      // We can accept input as long as register B is not full.
      // Note: flush_i and valid_i must not be high at the same time,
      // otherwise an invalid handshake may occur
      assign ready_o[i] = !a_full_q[i] || !b_full_q[i];

      // The unit provides output as long as one of the registers is filled.
      assign valid_o[i] = a_full_q[i] | b_full_q[i];

      // We empty the spill register before the slice register.
      assign data_o_tmr[i] = b_full_q[i] ? b_data_q : a_data_q;
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( $bits(T) ),
      .VoterType ( 1 ) // KP_MV
    ) i_data_o_tmr (
      .a_i              ( data_o_tmr[0] ),
      .b_i              ( data_o_tmr[1] ),
      .c_i              ( data_o_tmr[2] ),
      .majority_o       ( data_o        ),
      .fault_detected_o ( faults[2]     )
    );


  end

endmodule
