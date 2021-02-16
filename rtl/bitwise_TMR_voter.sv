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
  parameter DataWidth = 32,
  parameter VoterType = 2 // 0: Classical_MV, 1: KP_MV, 2: BN_MV
) (
  input  logic [DataWidth-1:0] in_a,
  input  logic [DataWidth-1:0] in_b,
  input  logic [DataWidth-1:0] in_c,
  output logic [DataWidth-1:0] out,
  output logic error,
  output logic [2:0] error_cba
);
  
  logic [DataWidth-1:0] err_a_all, err_b_all, err_c_all;

  for (genvar i = 0; i < DataWidth; i++) begin
    TMR_voter_detect #(
      .VoterType ( VoterType )
    ) voter_i (
      .in_a (in_a[i]),
      .in_b (in_b[i]),
      .in_c (in_c[i]),
      .out  (out[i]),
      .error_cba ( { err_c_all[i], err_b_all[i], err_a_all[i] } )
    );
  end

  assign error_cba[0] = |err_a_all;
  assign error_cba[1] = |err_b_all;
  assign error_cba[2] = |err_c_all;
  // assign error = error_cba[0] && error_cba[1] || error_cba[0] && error_cba[2] || error_cba[1] && error_cba[2];

  TMR_voter #(
    .VoterType(0)
  ) triple_mismatch (
    .in_a(error_cba[0]),
    .in_b(error_cba[1]),
    .in_c(error_cba[2]),
    .out (error)
  );

endmodule

