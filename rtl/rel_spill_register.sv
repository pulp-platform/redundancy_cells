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
    logic [10:0] faults;
    assign fault_o = |faults;

    logic [2:0] valid_in, ready_out, valid_out, ready_in;
    if (TmrHandshake) begin : gen_tmr_handshake
      assign valid_in  = valid_i;
      assign ready_o = ready_out;
      assign valid_o = valid_out;
      assign ready_in  = ready_i;
      assign faults[1:0] = '0;
    end else begin : gen_non_tmr_handshake
      assign valid_in  = {3{valid_i}};
      assign ready_in  = {3{ready_i}};
      TMR_voter_fail #(
        .VoterType ( 0 ) // Classical_MV
      ) i_ready_tmr (
        .a_i              ( ready_out[0] ),
        .b_i              ( ready_out[1] ),
        .c_i              ( ready_out[2] ),
        .majority_o       ( ready_o      ),
        .fault_detected_o ( faults[0]    )
      );
      TMR_voter_fail #(
        .VoterType ( 0 ) // Classical_MV
      ) i_valid_tmr (
        .a_i              ( valid_out[0] ),
        .b_i              ( valid_out[1] ),
        .c_i              ( valid_out[2] ),
        .majority_o       ( valid_o      ),
        .fault_detected_o ( faults[1]    )
      );
    end

    // The A register.
    T a_data_d, a_data_q;
    T [2:0] a_data_d_tmr;
    // logic [2:0] a_full_q, a_full_q_tmr;
    // logic [2:0] a_fill, a_drain;

    // The B register.
    T b_data_d, b_data_q;
    T [2:0] b_data_d_tmr;
    // logic [2:0] b_full_q, b_full_q_tmr;
    // logic [2:0] b_fill, b_drain;

    T [2:0] data_o_tmr;

    logic [2:0] a_full_q_sync, b_full_q_sync;
    logic [2:0][1:0] alt_a_full_q_sync, alt_b_full_q_sync;

    for (genvar i = 0; i < 3; i++) begin : gen_tmr_part
      for (genvar j = 0; j < 2; j++) begin : gen_sync
        assign alt_a_full_q_sync[i][j] = a_full_q_sync[(i+j+1) % 3];
        assign alt_b_full_q_sync[i][j] = b_full_q_sync[(i+j+1) % 3];
      end
      (* dont_touch *)
      rel_spill_reg_tmr_part #(
        .T           ( T ),
        .Bypass      ( Bypass )
      ) i_tmr_part (
        .clk_i              ( clk_i              ),
        .rst_ni             ( rst_ni             ),
        .data_i             ( data_i             ),
        .a_data_q           ( a_data_q           ),
        .a_data_d           ( a_data_d_tmr[i]    ),
        .alt_a_full_q_sync  ( alt_a_full_q_sync[i] ),
        .a_full_q_sync      ( a_full_q_sync[i] ),
        .b_data_q           ( b_data_q           ),
        .b_data_d           ( b_data_d_tmr[i]    ),
        .alt_b_full_q_sync  ( alt_b_full_q_sync[i] ),
        .b_full_q_sync      ( b_full_q_sync[i] ),
        .data_o             ( data_o_tmr[i]      ),
        .valid_i            ( valid_in[i]        ),
        .valid_o            ( valid_out[i]       ),
        .ready_i            ( ready_in[i]        ),
        .ready_o            ( ready_out[i]       ),
        .faults             ( faults[3+2*i:2+2*i] )
      );
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( $bits(T) ),
      .VoterType ( 1 ) // KP_MV
    ) i_a_data_tmr (
      .a_i              ( a_data_d_tmr[0] ),
      .b_i              ( a_data_d_tmr[1] ),
      .c_i              ( a_data_d_tmr[2] ),
      .majority_o       ( a_data_d        ),
      .fault_detected_o ( faults[8]       )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_data
      if (!rst_ni)
        a_data_q <= '0;
      else
        a_data_q <= a_data_d;
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( $bits(T) ),
      .VoterType ( 1 ) // KP_MV
    ) i_b_data_tmr (
      .a_i              ( b_data_d_tmr[0] ),
      .b_i              ( b_data_d_tmr[1] ),
      .c_i              ( b_data_d_tmr[2] ),
      .majority_o       ( b_data_d        ),
      .fault_detected_o ( faults[9]       )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_data
      if (!rst_ni)
        b_data_q <= '0;
      else
        b_data_q <= b_data_d;
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( $bits(T) ),
      .VoterType ( 1 ) // KP_MV
    ) i_data_o_tmr (
      .a_i              ( data_o_tmr[0] ),
      .b_i              ( data_o_tmr[1] ),
      .c_i              ( data_o_tmr[2] ),
      .majority_o       ( data_o        ),
      .fault_detected_o ( faults[10]     )
    );
  end

endmodule

(* no_ungroup *)
(* no_boundary_optimization *)
module rel_spill_reg_tmr_part #(
  parameter type T           = logic, // Assumed ECC protected
  parameter bit  Bypass      = 1'b0

) (
  input  logic clk_i,
  input  logic rst_ni,
  input  T data_i,
  input  T a_data_q,
  output T a_data_d,
  input  logic [1:0] alt_a_full_q_sync,
  output logic a_full_q_sync,
  input  T b_data_q,
  output T b_data_d,
  input  logic [1:0] alt_b_full_q_sync,
  output logic b_full_q_sync,
  output T data_o,
  input  logic valid_i,
  output logic valid_o,
  input  logic ready_i,
  output logic ready_o,
  output logic [1:0] faults
);

  logic a_full_q;
  logic a_fill, a_drain;

  assign a_data_d = a_fill ? data_i : a_data_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_data
    if (!rst_ni)
      a_full_q_sync <= '0;
    else if (a_fill || a_drain)
      a_full_q_sync <= a_fill;
  end

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_a_full_tmr (
    .a_i              ( a_full_q_sync ),
    .b_i              ( alt_a_full_q_sync[0] ),
    .c_i              ( alt_a_full_q_sync[1] ),
    .majority_o       ( a_full_q ),
    .fault_detected_o ( faults[0] )
  );

  logic b_full_q;
  logic b_fill, b_drain;

  assign b_data_d = b_fill ? a_data_q : b_data_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_data
    if (!rst_ni)
      b_full_q_sync <= '0;
    else if (b_fill || b_drain)
      b_full_q_sync <= b_fill;
  end

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_b_full_tmr (
    .a_i              ( b_full_q_sync ),
    .b_i              ( alt_b_full_q_sync[0] ),
    .c_i              ( alt_b_full_q_sync[1] ),
    .majority_o       ( b_full_q ),
    .fault_detected_o ( faults[1] )
  );

  // Fill the A register when the A or B register is empty. Drain the A register
  // whenever it is full and being filled, or if a flush is requested.
  assign a_fill = valid_i && ready_o;
  assign a_drain = (a_full_q && !b_full_q);

  // Fill the B register whenever the A register is drained, but the downstream
  // circuit is not ready. Drain the B register whenever it is full and the
  // downstream circuit is ready, or if a flush is requested.
  assign b_fill = a_drain && (!ready_i);
  assign b_drain = (b_full_q && ready_i);

  // We can accept input as long as register B is not full.
  // Note: flush_i and valid_i must not be high at the same time,
  // otherwise an invalid handshake may occur
  assign ready_o = !a_full_q || !b_full_q;

  // The unit provides output as long as one of the registers is filled.
  assign valid_o = a_full_q | b_full_q;

  // We empty the spill register before the slice register.
  assign data_o = b_full_q ? b_data_q : a_data_q;

endmodule
