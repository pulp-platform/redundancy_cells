// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// 
// Triple Modular Redundancy Majority Voter (MV) for a data word
// 
// based on https://doi.org/10.1109/VTEST.2000.843880

module TMR_word_voter #(
  parameter DATA_WIDTH = 32
) (
  input  logic [DATA_WIDTH-1:0] in_a,
  input  logic [DATA_WIDTH-1:0] in_b,
  input  logic [DATA_WIDTH-1:0] in_c,
  output logic [DATA_WIDTH-1:0] out,
  output logic                  error
);

  logic match_ab, match_bc, match_ac;

  assign match_ab = &(in_a~^in_b);
  assign match_bc = &(in_b~^in_c);
  assign match_ac = &(in_a~^in_c);
  assign error = ~(match_ab | match_bc | match_ac);

  assign out = (match_ac&&in_a)|(~match_ac&&in_b);

endmodule

