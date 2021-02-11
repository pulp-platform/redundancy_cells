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
// Triple Modular Redundancy Majority Voter (MV) for a single bit, with indication of erroneous bit

module TMR_voter_detect #(
  parameter VOTER_TYPE = 0 // 0: Classical_MV, 1: KP_MV, 2: BN_MV
) (
  input  logic in_a,
  input  logic in_b,
  input  logic in_c,
  output logic out,
  output logic err_a,
  output logic err_b,
  output logic err_c
);

  TMR_voter #(
    .VOTER_TYPE ( VOTER_TYPE )
  ) voter (
    .in_a,
    .in_b,
    .in_c,
    .out
  );

  assign err_a = (in_a ^ out);
  assign err_b = (in_b ^ out);
  assign err_c = (in_c ^ out); 

endmodule
