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

module tb_tmr_voter_test;

  localparam time TTest  = 8ns;
  localparam time TApply = 2ns;

  logic [2:0] in;
  logic       out_classic;
  logic       out_kp;
  logic       out_bn;

  TMR_voter #(.VOTER_TYPE(0)) tmr_classic (
    .in_a(in[0]      ),
    .in_b(in[1]      ),
    .in_c(in[2]      ),
    .out (out_classic)
  );

  TMR_voter #(.VOTER_TYPE(1)) tmr_kp (
    .in_a(in[0] ),
    .in_b(in[1] ),
    .in_c(in[2] ),
    .out (out_kp)
  );

  TMR_voter #(.VOTER_TYPE(2)) tmr_bn (
    .in_a(in[0] ),
    .in_b(in[1] ),
    .in_c(in[2] ),
    .out (out_bn)
  );

  initial begin
    in = 3'b000;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    #TApply
    in = 3'b001;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    #TApply
    in = 3'b010;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    #TApply
    in = 3'b100;
    #TTest
    assert(out_classic == 1'b0);
    assert(out_kp      == 1'b0);
    assert(out_bn      == 1'b0);
    #TApply

    in = 3'b111;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    #TApply
    in = 3'b110;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    #TApply
    in = 3'b101;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
    #TApply
    in = 3'b011;
    #TTest
    assert(out_classic == 1'b1);
    assert(out_kp      == 1'b1);
    assert(out_bn      == 1'b1);
  end

endmodule

