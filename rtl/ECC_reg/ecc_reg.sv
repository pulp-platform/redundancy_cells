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

// Description:
// This module implements an ECC protected register with variable data width,
// multiple code options, optional encoding, decoding and correction capabilities,
// and many variants for the FF. All options can be seen below.
// DataWidth: The number of data bits to be stored in the ECC register
// NumErrorDetect: The number of errors the register should be able to detect.
//                 The EC Code will be selected according to this parameter.
// NumErrorCorrect: The number of errors the register should be able to correct.
//                  The EC Code will be selected according to this parameter.
// Encode: if enabled: The ECC register will use the unencoded data provided on
//                     the 'data_i' port and encode it before storing it.
// Encode: if disabled: The ECC register will directly store the data provided
//                      on 'data_i' and assume it was correctly encoded by the
//                      user. It is suggested to use the 'ecc_enc' module to
//                      encode the data for compatibility.
// Decode: if enabled: The data stored in the Register will be decoded before
//                     it is provided on 'data_o'. If the selected code has
//                     error correction capability, all possible errors will be
//                     corrected before the data is provided on the output.
//                     Note that this will introduce quite some latency to the
//                     Register.
// Decode: if disabled: The stored data will be directly provided on 'data_o',
//                      without correction. The user can use the error output
//                      signals to see if the output is valid or not. When decode
//                      is disabled, 'data_o' consists of both the data bits and
//                      the ecc bits. If the user is only interested in the data
//                      bits, the parameter 'OutputECCBits' can be set to 0.
// SelfCorrect: if enabled: The register will automatically correct the stored
//                          data according to the 'NumErrorCorrect' parameter.
//                          The correction will be done automatically in one
//                          clock cycle. During this time, the FF will not
//                          accept any new data on its input. The module
//                          indicates an ongoing correction by setting
//                          'error_correctable_o' to '1' duriing the correction.
//                          This behaviour is only bypassed if the FF has a load
//                          and 'load_en_i' is '1' during the correction cycle.
//                          In this case, the new data on 'data_i' will be stored
//                          and the old, incorrect data will be disregarded.
// SelfCorrect: if disabled: Data in the FF will not be corrected. If the stored
//                           data contains errors, the corresponding error signals
//                           will indicate this.
// Note that error detection is always enabled and the 'error_correctable_o' and
// 'error_uncorrectable_o' will always be valid, independent of the parameters.


// register macros
`include "common_cells/registers.svh"
`include "ECC_reg/ecc_calc.svh"

module ecc_reg #(
  // Data Settings
  parameter int unsigned DataWidth = 0,
  // ECC Settings
  parameter int unsigned NumErrorDetect = 1,
  parameter int unsigned NumErrorCorrect = 0,
  parameter bit Encode = 1,
  parameter bit Decode = 1,
  parameter bit SelfCorrect = 1,
  parameter bit OutputECCBits = 1,
  // FF Settings
  parameter bit HasReset = 1,
  parameter bit AsynchronousReset = 1,
  parameter bit ActiveLowReset = 1,
  parameter bit HasLoad = 0,
  // Dependent Parameters, do not change
  parameter int unsigned EccDist = `ECC_DIST(NumErrorCorrect, NumErrorDetect),
  parameter int          EccWidth = `ECC_WIDTH(DataWidth, EccDist),
  parameter int unsigned InputWidth  = DataWidth + (Encode                    ? 0 : EccWidth),
  parameter int unsigned OutputWidth = DataWidth + ((Decode | !OutputECCBits) ? 0 : EccWidth)
) (
  // clock and reset inputs
  input  logic                  clk_i,
  input  logic                  rst_ni,
  // data ports
  input  logic[ InputWidth-1:0] data_i,
  input  logic[ InputWidth-1:0] reset_value_i,
  output logic[OutputWidth-1:0] data_o,
  // ECC ports
  output logic                  error_correctable_o,
  output logic                  error_uncorrectable_o,
  // FF ports
  input  logic                  load_en_i
);

/******************
 *     Encode     *
 ******************/

logic [EccWidth+DataWidth-1:0] data_encoded, reset_value_encoded;

if ( Encode ) begin : enc
  // Encode the incomming data
  ecc_enc #(
    .DataWidth       ( DataWidth       ),
    .NumErrorDetect  ( NumErrorDetect  ),
    .NumErrorCorrect ( NumErrorCorrect )
  ) i_enc (
    .data_i (data_i      ),
    .data_o (data_encoded)
  );
  // Encode the reset value
  ecc_enc #(
    .DataWidth       ( DataWidth       ),
    .NumErrorDetect  ( NumErrorDetect  ),
    .NumErrorCorrect ( NumErrorCorrect )
  ) i_enc_rst_val (
    .data_i (reset_value_i      ),
    .data_o (reset_value_encoded)
  );
end else begin : no_enc
  assign data_encoded = data_i;
  assign reset_value_encoded = reset_value_i;
end

/*******************
 * FF input select *
 *******************/

logic [EccWidth+DataWidth-1:0] data_d, data_q, data_corrected;

if(HasLoad && SelfCorrect) begin
  assign data_d = load_en_i ? data_encoded : data_corrected;
end else if(HasLoad && ~SelfCorrect) begin
  assign data_d = load_en_i ? data_encoded : data_q;
end else if(~HasLoad && SelfCorrect) begin
  assign data_d = error_correctable_o ? data_corrected : data_encoded;
end else begin
  assign data_d = data_encoded;
end

/*****************
 *   Flip-Flop   *
 *****************/

if ( HasReset &&  AsynchronousReset &&  ActiveLowReset && ~HasLoad) begin
  `FF(data_q, data_d, reset_value_encoded, clk_i, rst_ni)
end else if ( HasReset &&  AsynchronousReset && ~ActiveLowReset && ~HasLoad) begin
  `FFAR(data_q, data_d, reset_value_encoded, clk_i, ~rst_ni)
end else if ( HasReset && ~AsynchronousReset && ~ActiveLowReset && ~HasLoad) begin
  `FFSR(data_q, data_d, reset_value_encoded, clk_i, ~rst_ni)
end else if ( HasReset && ~AsynchronousReset &&  ActiveLowReset && ~HasLoad) begin
 `FFSRN(data_q, data_d, reset_value_encoded, clk_i, rst_ni)
end else if ( ~HasReset && ~HasLoad) begin
 `FFNR(data_q, data_d, clk_i)
end else if ( HasReset &&  AsynchronousReset &&  ActiveLowReset && HasLoad) begin
 `FFL(data_q, data_d, load_en_i, reset_value_encoded, clk_i, rst_ni)
end else if ( HasReset &&  AsynchronousReset && ~ActiveLowReset && HasLoad) begin
 `FFLAR(data_q, data_d, load_en_i, reset_value_encoded, clk_i, ~rst_ni)
end else if ( HasReset && ~AsynchronousReset && ~ActiveLowReset && HasLoad) begin
 `FFLSR(data_q, data_d, load_en_i, reset_value_encoded, clk_i, ~rst_ni)
end else if ( HasReset && ~AsynchronousReset &&  ActiveLowReset && HasLoad) begin
 `FFLSRN(data_q, data_d, load_en_i, reset_value_encoded, clk_i, rst_ni)
end else if ( ~HasReset && HasLoad) begin
 `FFLNR(data_q, data_d, load_en_i, clk_i)
end

/****************
 *  Correction  *
 ****************/

// The 'correction' part is only used if Decode or SelfCorrect is enabled.
// When both are disabled, only the detection segment of the corrector is used.

ecc_cor #(
  .DataWidth      (DataWidth      ),
  .NumErrorDetect (NumErrorDetect ),
  .NumErrorCorrect(NumErrorCorrect)
) i_cor (
  .data_i                (data_q               ),
  .data_o                (data_corrected       ),
  .error_correctable_o   (error_correctable_o  ),
  .error_uncorrectable_o (error_uncorrectable_o)
);

/*******************
 *  Output Assign  *
 *******************/

if(Decode) begin
  assign data_o = data_corrected;
end else begin
  if(OutputECCBits) begin
    assign data_o = data_q;
  end else begin
    assign data_o = data_q[DataWidth-1:0];
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
