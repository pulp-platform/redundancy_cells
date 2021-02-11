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

module bitwise_TMR_voter #(
  parameter DATA_WIDTH = 32,
  parameter VOTER_TYPE = 0 // 0: Classical_MV, 1: KP_MV, 2: BN_MV
) (
  input  logic [DATA_WIDTH-1:0] in_a,
  input  logic [DATA_WIDTH-1:0] in_b,
  input  logic [DATA_WIDTH-1:0] in_c,
  output logic [DATA_WIDTH-1:0] out,
  output logic err_a,
  output logic err_b,
  output logic err_c,
  output logic error
);
  
  logic [DATA_WIDTH-1:0] err_a_all, err_b_all, err_c_all;

  for (genvar i = 0; i < DATA_WIDTH; i++) begin
    TMR_voter_detect #(
      .VOTER_TYPE ( VOTER_TYPE )
    ) voter_i (
      .in_a (in_a[i]),
      .in_b (in_b[i]),
      .in_c (in_c[i]),
      .out  (out[i]),
      .err_a(err_a_all[i]),
      .err_b(err_b_all[i]),
      .err_c(err_c_all[i])
    );
  end

  assign err_a = |err_a_all;
  assign err_b = |err_b_all;
  assign err_c = |err_c_all;
  assign error = err_a && err_b || err_a && err_c || err_b && err_c;

endmodule

