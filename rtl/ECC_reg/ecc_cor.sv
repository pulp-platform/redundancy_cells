// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Luca Rufer (lrufer@student.ethz.ch)

// Description: Module to correct Data with Error Correcting Codes (ECC).
// When using this module, make sure the data was encoded using the
// ecc_enc.sv module for compatibility.
// This Module can also be used as a decoder or detector
// For Decoding, only use the lower 'DataWidth' bits of the 'data_o' output.
// For Detecting, don't use the 'data_o' port. Especially for codes with large
// distances, the correction part of the module can become huge.
// Only certain data widths and codes are supported. Typically, at least
// 500 bits datawidth are supported per code. For longer data widths, there
// are other, better suited codes than the ones used here.
// The following codes are implemented:
// D = 1: No Encoding: No Detection possible
// D = 2: Even Parity: Single Error Detection (SED)
// D = 3: Hamming:     Single Error Correction (SEC) or
//                     Double Error Detection (DED)
// D = 4: Even Parity: Single Error Correction (SEC) + Double Error Detection (DED) or
//                     Tripple Error Detection (TED)
// ECC can be disabled by setting both 'NumErrorDetect' and 'NumErrorCorrect'.
// In this case, the Module just outputs the input data again and sets the
// error signals to 0.

// include ECC macros for calculations
`include "ECC_reg/ecc_calc.svh"

module ecc_cor #(
  // Data Settings
  parameter int unsigned DataWidth = 0,
  // ECC Settings
  parameter int unsigned NumErrorDetect = 1,
  parameter int unsigned NumErrorCorrect = 0,
  // Dependent Parameters, do not change
  parameter int unsigned EccDist = `ECC_DIST(NumErrorCorrect, NumErrorDetect),
  parameter int          EccWidth = `ECC_WIDTH(DataWidth, EccDist)
) (
  // Data ports
  input  logic[EccWidth+DataWidth-1:0] data_i,
  output logic[EccWidth+DataWidth-1:0] data_o,
  // ECC ports
  output logic error_correctable_o,
  output logic error_uncorrectable_o
);

// Not all codes are implemented for all bit widths. For encoding and decoding,
// 0s are appended to the data to increase the width to the next supported size.
localparam int unsigned ZeroForcedWidth =
  (EccDist == 1) ? 0 : // No ECC
  (EccDist == 2) ? 0 : // Parity
  (EccDist == 3) ? 0 : // Hamming Code
  (EccDist == 4) ? ( // Hsiao Code
    (DataWidth ==   8) ? 0 :
    (DataWidth ==  16) ? 0 :
    (DataWidth ==  32) ? 0 :
    (DataWidth ==  64) ? 0 :
    (DataWidth <=   1) ? (  1 - DataWidth) :
    (DataWidth <=   4) ? (  4 - DataWidth) :
    (DataWidth <=  11) ? ( 11 - DataWidth) :
    (DataWidth <=  26) ? ( 26 - DataWidth) :
    (DataWidth <=  57) ? ( 57 - DataWidth) :
    (DataWidth <= 120) ? (120 - DataWidth) :
    (DataWidth <= 247) ? (247 - DataWidth) :
                         (502 - DataWidth)
  ) : 0;

/****************
 *  Correction  *
 ****************/

logic [EccWidth+DataWidth+ZeroForcedWidth-1:0] data_in_padded;
logic [EccWidth+DataWidth+ZeroForcedWidth-1:0] data_out_padded;

logic [EccWidth-1:0] syndrome;
logic [EccWidth+DataWidth-1:0] data_corrected;

assign data_in_padded = {data_i, {ZeroForcedWidth{1'b0}}};

if ( EccDist == 1) begin : dec_no_ecc
  assign data_o = data_i;
end else if ( EccDist == 2 ) begin : dec_parity
  assign syndrome = ^data_i;
  assign data_o = data_i;
end else if ( EccDist == 3 ) begin : dec_hamming
  prim_hamming_cor #(
    .DataWidth (DataWidth)
  ) i_cor (
    .data_i     (data_i        ),
    .data_o     (data_corrected),
    .syndrome_o (syndrome      ),
    .error_o    (              )
  );
end else if ( EccDist == 4 ) begin : dec_hsiao
  if(DataWidth ==   8) begin
    prim_secded_13_8_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth ==  16) begin
    prim_secded_22_16_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth ==  32) begin
    prim_secded_39_32_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth ==  64) begin
    prim_secded_72_64_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <=   1) begin
    prim_secded_4_1_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <=   4) begin
    prim_secded_8_4_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <=  11) begin
    prim_secded_16_11_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <=  26) begin
    prim_secded_32_26_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <=  57) begin
    prim_secded_64_57_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <= 120) begin
    prim_secded_128_120_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else if(DataWidth <= 247) begin
    prim_secded_256_247_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end else begin
    prim_secded_512_502_cor i_cor (
      .d_i        (data_in_padded ),
      .d_o        (data_out_padded),
      .syndrome_o (syndrome       ),
      .err_o      (               )
    );
  end
end

// Remove padding
if(EccDist == 4) begin
  assign data_corrected = data_out_padded[EccWidth+DataWidth+ZeroForcedWidth-1:ZeroForcedWidth];
end

// Determine if correctable or uncorrectable
if (EccDist == 1) begin // no ECC
  assign error_correctable_o = '0;
  assign error_uncorrectable_o = '0;
end else if (EccDist == 2) begin // Parity
  assign error_correctable_o = '0;
  assign error_uncorrectable_o = syndrome;
end else if (EccDist == 3) begin // Hamming Code
  if (NumErrorCorrect == 1) begin
    assign error_correctable_o = |syndrome;
    assign error_uncorrectable_o = '0;
    assign data_o = data_corrected;
  end else begin
    assign error_correctable_o = '0;
    assign error_uncorrectable_o = |syndrome;
    assign data_o = data_i;
  end
end else if (EccDist == 4) begin // Hsiao Code
  if (NumErrorCorrect == 1) begin
    assign error_correctable_o = ^syndrome;
    assign error_uncorrectable_o = |syndrome & ~(^syndrome);
    assign data_o = data_corrected;
  end else begin
    assign error_correctable_o = '0;
    assign error_uncorrectable_o = |syndrome;
    assign data_o = data_i;
  end
end

// pragma translate_off
if (DataWidth == 0)
  $fatal(1, "[ECC Register] DataWidth was no specified");

if (EccDist > 4)
  $fatal(1, "[ECC Register] Unsupported ECC type: NumErrorDetect = %d, NumErrorCorrect = %d.",
    NumErrorDetect, NumErrorCorrect);

if (EccWidth == -1)
  $fatal(1, "[ECC Register] Unsupported DataWidth for ECC type: NumErrorDetect = %d, NumErrorCorrect = %d.",
    NumErrorDetect, NumErrorCorrect);
// pragma translate_on

endmodule
