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
// Testbench for TMR Word Voter

module tb_tmr_word_voter_test;

  localparam int unsigned RunCycles = 10000;
  localparam time         TTest     = 8ns;
  localparam time         TApply    = 2ns;
  localparam int unsigned DataWidth = 32;

  logic      [DataWidth-1:0] test;
  logic [2:0][DataWidth-1:0] in;
  logic      [DataWidth-1:0] out;
  logic                      error;
  logic [2:0]                error_cba;

  TMR_word_voter #(.DataWidth(DataWidth)) tmr_word_voter (
    .in_a     (in[0]),
    .in_b     (in[1]),
    .in_c     (in[2]),
    .out      (out),
    .error    (error),
    .error_cba(error_cba)
  );

  initial begin
    in = '0;
    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      #TApply
      test = $urandom();
      in[0] = #TApply test;
      in[1] = #TApply test;
      in[2] = #TApply test;
      #TTest
      assert(out == test);
      assert(error == 1'b0);
      assert(error_cba == 3'b000);
    end

    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      #TApply
      test = $urandom();
      in[0] = #TApply $urandom();
      in[1] = #TApply test;
      in[2] = #TApply test;
      #TTest
      assert(out == test);
      assert(error == 1'b0);
      assert(error_cba == 3'b001);
    end

    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      #TApply
      test = $urandom();
      in[0] = #TApply test;
      in[1] = #TApply $urandom();
      in[2] = #TApply test;
      #TTest
      assert(out == test);
      assert(error == 1'b0);
      assert(error_cba == 3'b010);
    end

    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      #TApply
      test = $urandom();
      in[0] = #TApply test;
      in[1] = #TApply test;
      in[2] = #TApply $urandom();
      #TTest
      assert(out == test);
      assert(error == 1'b0);
      assert(error_cba == 3'b100);
    end

    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      #TApply
      in[0] = #TApply $urandom();
      in[1] = #TApply $urandom();
      in[2] = #TApply $urandom();
      #TTest
      // assert(out == test);
      assert(error == 1'b1);
      // assert(error_cba != 3'b000);
    end
  end

endmodule

