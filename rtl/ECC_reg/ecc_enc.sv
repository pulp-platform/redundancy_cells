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

// Description: Module to encode Data with Error Correcting Codes (ECC).
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
// In this case, the Module just outputs the input data again.

// include ECC macros for calculations
`include "ECC_reg/ecc_calc.svh"

module ecc_enc #(
  // Data Settings
  parameter int unsigned DataWidth = 0,
  // ECC Settings
  parameter int unsigned NumErrorDetect = 1,
  parameter int unsigned NumErrorCorrect = 0,
  // Dependent Parameters, do not change
  parameter int unsigned EccDist = `ECC_DIST(NumErrorCorrect, NumErrorDetect),
  parameter int          EccWidth = `ECC_WIDTH(DataWidth, EccDist)
) (
  input  logic[         DataWidth-1:0] data_i,
  output logic[EccWidth+DataWidth-1:0] data_o
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

  /******************
  *     Encode     *
  ******************/

  // Additional nets for encodings that require padding
  logic [         DataWidth+ZeroForcedWidth-1:0] data_in_padded;
  logic [EccWidth+DataWidth+ZeroForcedWidth-1:0] data_out_padded;

  // Expand the data with zeros
  assign data_in_padded = {data_i, {ZeroForcedWidth{1'b0}}};

  if ( EccDist == 1 ) begin : noecc
    assign data_o = data_i;
  end else if ( EccDist == 2 ) begin : parity
    assign data_o = {^data_i, data_i};
  end else if ( EccDist == 3 ) begin : hamming
      prim_hamming_enc #(
        .DataWidth (DataWidth)
      ) i_enc (
        .data_i,
        .data_o
      );
  end else if ( EccDist == 4 ) begin : hsiao
    if(DataWidth ==   8) begin
      prim_secded_13_8_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth ==  16) begin
      prim_secded_22_16_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth ==  32) begin
      prim_secded_39_32_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth ==  64) begin
      prim_secded_72_64_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <=   1) begin
      prim_secded_4_1_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <=   4) begin
      prim_secded_8_4_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <=  11) begin
      prim_secded_16_11_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <=  26) begin
      prim_secded_32_26_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <=  57) begin
      prim_secded_64_57_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <= 120) begin
      prim_secded_128_120_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else if(DataWidth <= 247) begin
      prim_secded_256_247_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end else begin
      prim_secded_512_502_enc i_enc (
        .in (data_in_padded ),
        .out(data_out_padded)
      );
    end
  end

  // Remove the padded zeros again
  // This can only be done for a linear systematic code.
  if ( EccDist == 4 ) begin
    assign data_o = data_out_padded[EccWidth+DataWidth+ZeroForcedWidth-1:ZeroForcedWidth];
  end

  // pragma translate_off
  if (DataWidth == 0)
    $fatal(1, "[ECC Encode] DataWidth was no specified");

  if (EccDist > 4)
    $fatal(1, "[ECC Encode] Unsupported ECC type: NumErrorDetect = %d, NumErrorCorrect = %d.",
      NumErrorDetect, NumErrorCorrect);

  if (EccWidth == -1)
    $fatal(1, "[ECC Encode] Unsupported DataWidth for ECC type: NumErrorDetect = %d, NumErrorCorrect = %d.",
      NumErrorDetect, NumErrorCorrect);
  // pragma translate_on

endmodule
