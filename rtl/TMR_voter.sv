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
// Triple Modular Redundancy Majority Voter (MV) for a single bit
// 
// Classical_MV: standard and & or gates
// KP_MV:        Kshirsagar and Patrikar MV [https://doi.org/10.1016/j.microrel.2009.08.001]
// BN_MV:        Ban and Naviner MV         [https://doi.org/10.1109/NEWCAS.2010.5603933]

module TMR_voter #(
  parameter VOTER_TYPE = 0 // 0: Classical_MV, 1: KP_MV, 2: BN_MV
) (
  input  logic in_a,
  input  logic in_b,
  input  logic in_c,
  output logic out
);

  case (VOTER_TYPE)
    0: // Classical_MV
      assign out = (in_a & in_b) | (in_a & in_c) | (in_b & in_c);
    1: // KP_MV
      begin
        logic n_1, n_2, p;
        assign n_1 = in_a ^ in_b;
        assign n_2 = in_b ^ in_c;
        assign p = n_1 & ~n_2;
        assign out = p ? in_c : in_a;
      end
    2: // BN_MV
      begin
        logic n;
        assign n = in_a ^ in_b;
        assign out = n ? in_c : in_b;
      end
    default : assign out = (in_a & in_b) | (in_a & in_c) | (in_b & in_c);
  endcase

endmodule
