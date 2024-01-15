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
// Hsiao ECC encoder
// Based in part on work by lowRISC

module hsiao_ecc_enc #(
  parameter int unsigned DataWidth = 32,
  parameter int unsigned ProtWidth = 7,
  parameter int unsigned TotalWidth = DataWidth + ProtWidth
) (
  input  logic [ DataWidth-1:0] in,
  output logic [TotalWidth-1:0] out
);

  import hsiao_ecc_pkg::*;

  if (ProtWidth < $clog2(DataWidth)+2) $error("ProtWidth must be greater than $clog2(DataWidth)+2");

  localparam bit HsiaoMatrix [ProtWidth][TotalWidth] = hsiao_matrix(DataWidth, ProtWidth);
  localparam bit [ProtWidth-1:0][TotalWidth-1:0] HsiaoCodes = { << { HsiaoMatrix }};

  always_comb begin : proc_encode
    out[DataWidth-1:0] = in;
    for (int unsigned i = 0; i < ProtWidth; i++) begin
      out[DataWidth + i] = ^(in & HsiaoCodes[i][DataWidth-1:0]);
    end
  end

endmodule
