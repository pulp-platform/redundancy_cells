// Copyright 2024 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Hsiao ECC decoder
// Based in part on work by lowRISC

module hsiao_ecc_dec #(
  parameter int unsigned DataWidth = 32,
  parameter int unsigned ProtWidth = 7,
  parameter int unsigned TotalWidth = DataWidth + ProtWidth
) (
  input  logic [TotalWidth-1:0] in,
  output logic [ DataWidth-1:0] out,
  output logic [ ProtWidth-1:0] syndrome_o,
  output logic [           1:0] err_o
);

  import hsiao_ecc_pkg::*;

  if (ProtWidth < $clog2(DataWidth)+2) $error("ProtWidth must be greater than $clog2(DataWidth)+2");

  localparam bit HsiaoMatrix [ProtWidth][TotalWidth] = hsiao_matrix(DataWidth, ProtWidth);
  localparam bit [ ProtWidth-1:0][TotalWidth-1:0] HsiaoCodes = { << { HsiaoMatrix }};
  localparam bit [TotalWidth-1:0][ ProtWidth-1:0] CorrCodes =
                                          { << { transpose(HsiaoMatrix, ProtWidth, TotalWidth) }};

  logic single_error;

  for (genvar i = 0; i < ProtWidth; i++) begin : gen_syndrome
    assign syndrome_o[i] = ^(in & HsiaoCodes[i]);
  end

  for (genvar i = 0; i < DataWidth; i++) begin : gen_out
    assign out[i] = in[i] ^ (syndrome_o == CorrCodes[i]);
  end

  assign single_error = ^syndrome_o;
  assign err_o[0] = single_error;
  assign err_o[1] = ~single_error & (|syndrome_o);

endmodule
