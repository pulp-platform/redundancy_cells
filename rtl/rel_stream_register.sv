// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Reliable (TMR + ECC-scrubbed) version of stream_register.
// The stored word is assumed to be Hsiao SECDED protected:
// DataWidth is the unprotected payload width, and the register
// itself is TotalWidth = DataWidth + ProtWidth wide.

module rel_stream_register import hsiao_ecc_pkg::*; #(
  parameter int unsigned DataWidth     = 32,
  parameter int unsigned ProtWidth     = min_ecc(DataWidth),
  parameter int unsigned TotalWidth    = DataWidth + ProtWidth,
  parameter bit          Bypass        = 1'b0, // make this stream register transparent
  parameter bit          TmrHandshake  = 1'b0, // use TMR handshake
  parameter bit          DataCorrector = 1'b1, // scrub the stored word with Hsiao ECC correction
  parameter int unsigned HsWidth       = TmrHandshake ? 3 : 1 // width of the handshake signals
) (
  input  logic                  clk_i     ,
  input  logic                  rst_ni    ,
  input  logic                  clr_i     ,
  input  logic                  testmode_i,
  input  logic [HsWidth   -1:0] valid_i   ,
  output logic [HsWidth   -1:0] ready_o   ,
  input  logic [TotalWidth-1:0] data_i    ,
  output logic [HsWidth   -1:0] valid_o   ,
  input  logic [HsWidth   -1:0] ready_i   ,
  output logic [TotalWidth-1:0] data_o    ,
  output logic [1:0]            err_o       // [0]: correctable (scrubbed), [1]: uncorrectable
);

  if (Bypass) begin : gen_bypass
    assign valid_o = valid_i;
    assign ready_o = ready_i;
    assign data_o  = data_i;
    assign err_o   = '0;
  end else begin : gen_stream_reg
    logic rec_err;

    // 2 handshake-voter faults + 3 per-partition state faults + 1 per data bit
    logic [4+TotalWidth:0] faults;
    assign err_o[0] = rec_err | (|faults);

    logic [2:0] valid_in, ready_out, valid_out, ready_in;
    if (TmrHandshake) begin : gen_tmr_handshake
      assign valid_in = valid_i;
      assign ready_o  = ready_out;
      assign valid_o  = valid_out;
      assign ready_in = ready_i;
      assign faults[1:0] = '0;
    end else begin : gen_non_tmr_handshake
      assign valid_in = {3{valid_i}};
      assign ready_in = {3{ready_i}};
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

    // The (single) data register.
    logic [TotalWidth-1:0] data_d, data_q;

    logic [2:0][TotalWidth-1:0] fill_tmr;
    logic [2:0] full_q_sync;
    logic [2:0][1:0] alt_full_q_sync;

    for (genvar i = 0; i < 3; i++) begin : gen_tmr_part
      for (genvar j = 0; j < 2; j++) begin : gen_sync
        assign alt_full_q_sync[i][j] = full_q_sync[(i+j+1) % 3];
      end
      rel_stream_reg_tmr_part #(
        .TotalWidth ( TotalWidth ),
        .Bypass     ( Bypass     )
      ) i_tmr_part (
        .clk_i             ( clk_i               ),
        .rst_ni            ( rst_ni              ),
        .clr_i             ( clr_i               ),
        .alt_full_q_sync_i ( alt_full_q_sync[i]  ),
        .full_q_sync_o     ( full_q_sync[i]      ),
        .fill_tmr_o        ( fill_tmr[i]         ),
        .valid_i           ( valid_in[i]         ),
        .valid_o           ( valid_out[i]        ),
        .ready_i           ( ready_in[i]         ),
        .ready_o           ( ready_out[i]        ),
        .faults_o          ( faults[2+i]         )
      );
    end

    // ECC scrub path: whenever the register is not being loaded with fresh
    // external data, continuously reload the Hsiao-corrected version of its
    // own content back in. Only instantiated if DataCorrector is set.
    logic [TotalWidth-1:0] data_hold;

    if (DataCorrector) begin : gen_data_corrector
      logic [TotalWidth-1:0] data_corrector, data_corrected;

      assign data_corrector = data_q;

      hsiao_ecc_cor #(
        .DataWidth ( DataWidth )
      ) i_ecc_corr (
        .in         ( data_corrector        ),
        .out        ( data_corrected        ),
        .syndrome_o (                       ),
        .err_o      ( {err_o[1], rec_err}   )
      );

      assign data_hold = data_corrected;
    end else begin : gen_no_data_corrector
      assign err_o[1]  = 1'b0;
      assign rec_err   = 1'b0;
      assign data_hold = data_q;
    end

    for (genvar i = 0; i < TotalWidth; i++) begin : gen_muxes
      logic fill;
      TMR_voter_fail #(
        .VoterType ( 1 ) // KP_MV
      ) i_fill_tmr (
        .a_i              ( fill_tmr[0][i] ),
        .b_i              ( fill_tmr[1][i] ),
        .c_i              ( fill_tmr[2][i] ),
        .majority_o       ( fill           ),
        .fault_detected_o ( faults[5+i]    )
      );

      assign data_d[i] = fill ? data_i[i] : data_hold[i];
      assign data_o[i] = data_q[i];
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : ps_data
      if (!rst_ni)
        data_q <= '0;
      else if (clr_i)
        data_q <= '0;
      else
        data_q <= data_d;
    end
  end

endmodule

(* no_ungroup *)
(* no_boundary_optimization *)
module rel_stream_reg_tmr_part #(
  parameter int unsigned TotalWidth = 32,
  parameter bit          Bypass     = 1'b0
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clr_i,
  input  logic [1:0] alt_full_q_sync_i,
  output logic full_q_sync_o,
  output logic [TotalWidth-1:0] fill_tmr_o,
  input  logic valid_i,
  output logic valid_o,
  input  logic ready_i,
  output logic ready_o,
  output logic faults_o
);

  logic full_q;
  logic upd, fill;

  for (genvar i = 0; i < TotalWidth; i++) begin : gen_tmr_fill
    assign fill_tmr_o[i] = fill;
  end

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_full_tmr (
    .a_i              ( full_q_sync_o        ),
    .b_i              ( alt_full_q_sync_i[0] ),
    .c_i              ( alt_full_q_sync_i[1] ),
    .majority_o       ( full_q               ),
    .fault_detected_o ( faults_o             )
  );

  // ready_o is asserted whenever the downstream circuit is ready, or the
  // register is currently empty.
  assign ready_o = ready_i | ~full_q;
  assign valid_o = full_q;

  // The state register is updated (with valid_i, which may be 0 or 1)
  // whenever ready_o is high; the data register is only loaded when valid
  // data is actually being captured.
  assign upd  = ready_o;
  assign fill = valid_i & ready_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_full
    if (!rst_ni)
      full_q_sync_o <= 1'b0;
    else if (clr_i)
      full_q_sync_o <= 1'b0;
    else if (upd)
      full_q_sync_o <= valid_i;
  end

endmodule