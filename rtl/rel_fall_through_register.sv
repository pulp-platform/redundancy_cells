// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Maoyuan Cai <maoyuan.cai@unibo.it>

// Reliable version of `fall_through_register` from common_cells, see there for the
// functional description. Data is protected by Hsiao SECDED ECC, control FFs by TMR.
// SETs are not covered.

module rel_fall_through_register #(
    parameter type T = logic  // Vivado requires a default value for type parameters.
) (
    input  logic    clk_i,          // Clock
    input  logic    rst_ni,         // Asynchronous active-low reset
    input  logic    clr_i,          // Synchronous clear
    input  logic    testmode_i,     // Test mode to bypass clock gating
    // Input port
    input  logic    valid_i,
    output logic    ready_o,
    input  T        data_i,
    // Output port
    output logic    valid_o,
    input  logic    ready_i,
    output T        data_o,
    // Fault outputs
    output logic    ecc_correctable_o,   // single-bit ECC error on the stored word (corrected)
    output logic    ecc_uncorrectable_o, // double-bit ECC error on the stored word
    output logic    fifo_correctable_o   // rel_fifo internal TMR fault (masked)
);

    localparam int unsigned DataW    = $bits(T);
    localparam int unsigned ProtW    = hsiao_ecc_pkg::min_ecc(DataW);
    localparam int unsigned EccDataW = DataW + ProtW;

    logic                fifo_empty, fifo_full;
    logic [DataW-1:0]    data_raw_in, data_raw_out;
    logic [EccDataW-1:0] data_enc, data_enc_out;
    logic [1:0]          ecc_err;

    assign data_raw_in = data_i;

    hsiao_ecc_enc #(
        .DataWidth ( DataW ),
        .ProtWidth ( ProtW )
    ) i_ecc_enc (
        .in  ( data_raw_in ),
        .out ( data_enc    )
    );

    rel_fifo #(
        .FallThrough ( 1'b1     ),
        .DataWidth   ( EccDataW ),
        .Depth       ( 1        )
    ) i_fifo (
        .clk_i,
        .rst_ni,
        .flush_i    ( clr_i                  ),
        .testmode_i,
        .full_o     ( fifo_full              ),
        .empty_o    ( fifo_empty             ),
        .usage_o    (                        ),
        .data_i     ( data_enc               ),
        .push_i     ( valid_i & ~fifo_full   ),
        .data_o     ( data_enc_out           ),
        .pop_i      ( ready_i & ~fifo_empty  ),
        .fault_o    ( fifo_correctable_o     )
    );

    hsiao_ecc_dec #(
        .DataWidth ( DataW ),
        .ProtWidth ( ProtW )
    ) i_ecc_dec (
        .in         ( data_enc_out ),
        .out        ( data_raw_out ),
        .syndrome_o (              ),
        .err_o      ( ecc_err      )
    );

    assign data_o = T'(data_raw_out);
    // ecc_err is only meaningful while the FIFO holds valid data
    assign ecc_correctable_o   = valid_o & ecc_err[0];
    assign ecc_uncorrectable_o = valid_o & ecc_err[1];

    assign ready_o = ~fifo_full;
    assign valid_o = ~fifo_empty;

endmodule
