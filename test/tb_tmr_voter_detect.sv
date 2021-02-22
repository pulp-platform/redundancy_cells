// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// 
// Testbench for TMR Voter

module tb_tmr_voter_detect;

  localparam time TTest  = 8ns;
  localparam time TApply = 2ns;

  logic [2:0] in;
  logic       out_classic;
  logic       out_kp;
  logic       out_bn;
  logic [2:0] error_classic;
  logic [2:0] error_kp;
  logic [2:0] error_bn;

  TMR_voter_detect #(
    .VoterType( 0 )
  ) tmr_classic (
    .a_i         ( in[0]         ),
    .b_i         ( in[1]         ),
    .c_i         ( in[2]         ),
    .majority_o  ( out_classic   ),
    .error_cba_o ( error_classic )
  );

  TMR_voter_detect #(
    .VoterType( 1 )
  ) tmr_kp (
    .a_i         ( in[0]    ),
    .b_i         ( in[1]    ),
    .c_i         ( in[2]    ),
    .majority_o  ( out_kp   ),
    .error_cba_o ( error_kp )
  );

  TMR_voter_detect #(
    .VoterType( 2 )
  ) tmr_bn (
    .a_i         ( in[0]    ),
    .b_i         ( in[1]    ),
    .c_i         ( in[2]    ),
    .majority_o  ( out_bn   ),
    .error_cba_o ( error_bn )
  );

  initial begin
    in = 3'b000;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    assert(error_classic == 3'b000);
    assert(error_kp == 3'b000);
    assert(error_bn == 3'b000);
    #TApply
    in = 3'b001;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    assert(error_classic == 3'b001);
    assert(error_kp == 3'b001);
    assert(error_bn == 3'b001);
    #TApply
    in = 3'b010;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    assert(error_classic == 3'b010);
    assert(error_kp == 3'b010);
    assert(error_bn == 3'b010);
    #TApply
    in = 3'b100;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    assert(error_classic == 3'b100);
    assert(error_kp == 3'b100);
    assert(error_bn == 3'b100);
    #TApply

    in = 3'b111;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    assert(error_classic == 3'b000);
    assert(error_kp == 3'b000);
    assert(error_bn == 3'b000);
    #TApply
    in = 3'b110;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    assert(error_classic == 3'b001);
    assert(error_kp == 3'b001);
    assert(error_bn == 3'b001);
    #TApply
    in = 3'b101;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    assert(error_classic == 3'b010);
    assert(error_kp == 3'b010);
    assert(error_bn == 3'b010);
    #TApply
    in = 3'b011;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    assert(error_classic == 3'b100);
    assert(error_kp == 3'b100);
    assert(error_bn == 3'b100);
  end

endmodule

