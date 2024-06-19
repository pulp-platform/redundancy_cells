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

`include "redundancy_cells/voters.svh"

module tb_voter_macros;

  /******************
   *  Helper tasks  *
   ******************/

  localparam time TTest  = 8ns;
  localparam time TApply = 2ns;

  task cycle_start();
    #TApply;
  endtask: cycle_start

  task cycle_end();
    #TTest;
  endtask: cycle_end

  /**********************
   *  Helper variables  *
   **********************/

  logic [2:0] in;

  logic       out_31, out_31f, out_31w;
  logic       fail_31f;
  logic [2:0] where_31w;
  logic       total_31w;

  logic [2:0] out_33, out_33f, out_33w;
  logic       fail_33f;
  logic [2:0] where_33w;
  logic       total_33w;

  // Parameterized Versions
  logic out_X1_3, out_X1_2, out_X1_1;
  logic out_X1f_3, out_X1f_2, out_X1f_1;
  logic fail_X1f_3, fail_X1f_2, fail_X1f_1;

  logic [2:0] out_XX_3, out_XX_2, out_XX_1;
  logic [2:0] out_XXf_3, out_XXf_2, out_XXf_1; 
  logic fail_XXf_3, fail_XXf_2, fail_XXf_1;


  // The same thing but with enums to ensure macros run fine with those
  typedef enum logic [1:0] {ZERO, ONE, TWO}  dummy_enum_t;

  dummy_enum_t [2:0] enum_in;

  dummy_enum_t       enum_out_31, enum_out_31f, enum_out_31w;
  logic              enum_fail_31f;
  logic [2:0]        enum_where_31w;
  logic              enum_total_31w;

  dummy_enum_t [2:0] enum_out_33, enum_out_33f, enum_out_33w;
  logic              enum_fail_33f;
  logic [2:0]        enum_where_33w;
  logic              enum_total_33w;

  // Parameterized Versions with Enums
  dummy_enum_t enum_out_X1_3, enum_out_X1_2, enum_out_X1_1;
  dummy_enum_t enum_out_X1f_3, enum_out_X1f_2, enum_out_X1f_1;
  logic enum_fail_X1f_3, enum_fail_X1f_2, enum_fail_X1f_1;

  dummy_enum_t [2:0] enum_out_XX_3, enum_out_XX_2, enum_out_XX_1;
  dummy_enum_t [2:0] enum_out_XXf_3, enum_out_XXf_2, enum_out_XXf_1; 
  logic enum_fail_XXf_3, enum_fail_XXf_2, enum_fail_XXf_1;

  /**********************
   *  DUTs              *
   **********************/

  `VOTE31 (in, out_31);
  `VOTE31F(in, out_31f, fail_31f);
  `VOTE31W(in, out_31w, where_31w, total_31w);

  `VOTE33 (in, out_33);
  `VOTE33F(in, out_33f, fail_33f);
  `VOTE33W(in, out_33w, where_33w, total_33w);

  // Parameterized Versions
  `VOTEX1F(3, in, out_X1f_3, fail_X1f_3);
  `VOTEX1F(2, in, out_X1f_2, fail_X1f_2);
  `VOTEX1F(1, in, out_X1f_1, fail_X1f_1);

  `VOTEX1 (3, in, out_X1_3);
  `VOTEX1 (2, in, out_X1_2);
  `VOTEX1 (1, in, out_X1_1);

  `VOTEXXF(3, in, out_XXf_3, fail_XXf_3);
  `VOTEXXF(2, in, out_XXf_2, fail_XXf_2);
  `VOTEXXF(1, in, out_XXf_1, fail_XXf_1);

  `VOTEXX (3, in, out_XX_3);
  `VOTEXX (2, in, out_XX_2);
  `VOTEXX (1, in, out_XX_1);

  // The same thing but with enums to ensure macros run fine with those
  `VOTE31 (enum_in, enum_out_31);
  `VOTE31F(enum_in, enum_out_31f, enum_fail_31f);
  `VOTE31W(enum_in, enum_out_31w, enum_where_31w, enum_total_31w);

  `VOTE33 (enum_in, enum_out_33);
  `VOTE33F(enum_in, enum_out_33f, enum_fail_33f);
  `VOTE33W(enum_in, enum_out_33w, enum_where_33w, enum_total_33w);

  // Parameterized Versions with Enums
  `VOTEX1 (3, enum_in, enum_out_X1_3);
  `VOTEX1 (2, enum_in, enum_out_X1_2);
  `VOTEX1 (1, enum_in, enum_out_X1_1);

  `VOTEX1F(3, enum_in, enum_out_X1f_3, enum_fail_X1f_3);
  `VOTEX1F(2, enum_in, enum_out_X1f_2, enum_fail_X1f_2);
  `VOTEX1F(1, enum_in, enum_out_X1f_1, enum_fail_X1f_1);

  `VOTEXX (3, enum_in, enum_out_XX_3);
  `VOTEXX (2, enum_in, enum_out_XX_2);
  `VOTEXX (1, enum_in, enum_out_XX_1);

  `VOTEXXF(3, enum_in, enum_out_XXf_3, enum_fail_XXf_3);
  `VOTEXXF(2, enum_in, enum_out_XXf_2, enum_fail_XXf_2);
  `VOTEXXF(1, enum_in, enum_out_XXf_1, enum_fail_XXf_1);

  /**********************
   *  Tests             *
   **********************/

  // Proc to group same outputs (Invariants)
  initial begin
    for (int cycle = 0; cycle < 8; cycle++) begin
      cycle_start();
      cycle_end();

      // 31 / X1 / XX and f / w versions are a subset of 33 versions
      assert(out_33f              === out_33);
      assert(out_33w              === out_33);
      assert(out_XX_3             === out_33);
      assert(out_XXf_3            === out_33);

      assert(out_31               === out_33[0]);
      assert(out_31f              === out_33[0]);
      assert(out_31w              === out_33[0]);
      assert(out_X1_3             === out_33[0]);
      assert(out_X1f_3            === out_33[0]);
      // -> out_33 needs per case testing

      // Out of lower dimension parameterizations are pass-through
      assert(out_XX_2[1:0]        === in[1:0]);
      assert(out_XX_1[0:0]        === in[0:0]);
      assert(out_XXf_2[1:0]       === in[1:0]);
      assert(out_XXf_1[0:0]       === in[0:0]);

      assert(out_X1_2             === in[0]);
      assert(out_X1_1             === in[0]);
      assert(out_X1f_2            === in[0]);
      assert(out_X1f_1            === in[0]);

      // Out of lower dimension parameterizations do not assign anything outside their range
      assert(out_XX_2[2:2]        === 1'bX);
      assert(out_XX_1[2:1]        === 2'bXX);
      assert(out_XXf_2[2:2]       === 1'bX);
      assert(out_XXf_1[2:1]       === 2'bXX);
      
      // Same for enums
      // 31 / X1 / XX and f / w versions are a subset of 33 versions
      assert(enum_out_33f         === enum_out_33);
      assert(enum_out_33w         === enum_out_33);
      assert(enum_out_XX_3        === enum_out_33);
      assert(enum_out_XXf_3       === enum_out_33);

      assert(enum_out_31          === enum_out_33[0]);
      assert(enum_out_31f         === enum_out_33[0]);
      assert(enum_out_31w         === enum_out_33[0]);
      assert(enum_out_X1_3        === enum_out_33[0]);
      assert(enum_out_X1f_3       === enum_out_33[0]);
      // -> enum_out_33 needs per case testing

      // Out of lower dimension parameterizations are pass-through
      assert(enum_out_XX_2[1:0]   === enum_in[1:0]);
      assert(enum_out_XX_1[0:0]   === enum_in[0:0]);
      assert(enum_out_XXf_2[1:0]  === enum_in[1:0]);
      assert(enum_out_XXf_1[0:0]  === enum_in[0:0]);

      assert(enum_out_X1_2        === enum_in[0]);
      assert(enum_out_X1_1        === enum_in[0]);
      assert(enum_out_X1f_2       === enum_in[0]);
      assert(enum_out_X1f_1       === enum_in[0]);

      // Out of lower dimension parameterizations do not assign anything outside their range
      assert(enum_out_XX_2[2:2]   === 2'bXX);
      assert(enum_out_XX_1[2:1]   === 4'bXXXX);
      assert(enum_out_XXf_2[2:2]  === 2'bXX);
      assert(enum_out_XXf_1[2:1]  === 4'bXXXX);

      // Fail signals with 3 inputs are the same
      assert(enum_fail_31f        === fail_31f);
      assert(fail_33f             === fail_31f);
      assert(enum_fail_33f        === fail_31f);
      assert(fail_X1f_3           === fail_31f);
      assert(fail_XXf_3           === fail_31f);
      assert(enum_fail_X1f_3      === fail_31f);
      assert(enum_fail_XXf_3      === fail_31f);
      // -> fail_31f needs per case testing

      // Fail signals with 2 inputs are the same
      assert(fail_XXf_2           === fail_X1f_2);
      assert(enum_fail_X1f_2      === fail_X1f_2);
      assert(enum_fail_XXf_2      === fail_X1f_2);
      // -> fail_X1f_2 needs per case testing

      // Fail signals with 1 input are constant 0
      assert(fail_X1f_1           === 1'b0);
      assert(fail_XXf_1           === 1'b0);
      assert(enum_fail_X1f_1      === 1'b0);
      assert(enum_fail_XXf_1      === 1'b0);

      // Where signals are always the same
      assert(enum_where_31w       === where_31w);
      assert(where_33w            === where_31w);
      assert(enum_where_33w       === where_31w);
      // -> where_31w needs per case testing

      // Total failure can only happen if all 3 things are different
      // For logic only this is not the case, so input always 0.
      assert(total_31w            === 1'b0);
      assert(total_31w            === 1'b0);
      // For enums however we can assign other values than ZERO and ONE
      assert(enum_total_33w       === enum_total_31w);
      // -> enum_total_31w needs per case testing

    end
  end

  // Proc to do actual testing
  initial begin
    cycle_start();
    in = 3'b000;
    enum_in = {ZERO, ZERO, ZERO};

    cycle_end();
    assert(out_33         === 3'b000);
    assert(enum_out_33    === {ZERO, ZERO, ZERO});

    assert(fail_31f       === 1'b0);
    assert(fail_X1f_2     === 1'b0);
    assert(where_31w      === 3'b000);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b001;
    enum_in = {ZERO, ZERO, ONE};

    cycle_end();
    assert(out_33         === 3'b000);
    assert(enum_out_33    === {ZERO, ZERO, ZERO});

    assert(fail_31f       === 1'b1);
    assert(fail_X1f_2     === 1'b1);
    assert(where_31w      === 3'b001);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b010;
    enum_in = {ZERO, ONE, ZERO};

    cycle_end();
    assert(out_33         === 3'b000);
    assert(enum_out_33    === {ZERO, ZERO, ZERO});

    assert(fail_31f       === 1'b1);
    assert(fail_X1f_2     === 1'b1);
    assert(where_31w      === 3'b010);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b100;
    enum_in = {ONE, ZERO, ZERO};

    cycle_end();
    assert(out_33         === 3'b000);
    assert(enum_out_33    === {ZERO, ZERO, ZERO});

    assert(fail_31f       === 1'b1);
    assert(fail_X1f_2     === 1'b0);
    assert(where_31w      === 3'b100);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b111;
    enum_in = {ONE, ONE, ONE};

    cycle_end();
    assert(out_33         === 3'b111);
    assert(enum_out_33    === {ONE, ONE, ONE});

    assert(fail_31f       === 1'b0);
    assert(fail_X1f_2     === 1'b0);
    assert(where_31w      === 3'b000);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b110;
    enum_in = {ONE, ONE, ZERO};

    cycle_end();
    assert(out_33         === 3'b111);
    assert(enum_out_33    === {ONE, ONE, ONE});

    assert(fail_31f       === 1'b1);
    assert(fail_X1f_2     === 1'b1);
    assert(where_31w      === 3'b001);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b101;
    enum_in = {ONE, ZERO, ONE};

    cycle_end();
    assert(out_33         === 3'b111);
    assert(enum_out_33    === {ONE, ONE, ONE});

    assert(fail_31f       === 1'b1);
    assert(fail_X1f_2     === 1'b1);
    assert(where_31w      === 3'b010);
    assert(enum_total_31w === 1'b0);

    cycle_start();
    in = 3'b011;
    enum_in = {ZERO, ONE, ONE};

    cycle_end();
    assert(out_33        === 3'b111);
    assert(enum_out_33   === {ONE, ONE, ONE});

    assert(fail_31f       === 1'b1);
    assert(fail_X1f_2     === 1'b0);
    assert(where_31w      === 3'b100);
    assert(enum_total_31w === 1'b0);

  // Check that the total fault works
  cycle_start();
  enum_in = {ZERO, ONE, TWO};

  cycle_end();
  assert(enum_total_31w === 1'b1);

  cycle_start();
  enum_in = {ZERO, TWO, ONE};

  cycle_end();
  assert(enum_total_31w === 1'b1);

  cycle_start();
  enum_in = {ONE, ZERO, TWO};

  cycle_end();
  assert(enum_total_31w === 1'b1);

  cycle_start();
  enum_in = {ONE, TWO, ZERO};

  cycle_end();
  assert(enum_total_31w === 1'b1);

  cycle_start();
  enum_in = {TWO, ZERO, ONE};

  cycle_end();
  assert(enum_total_31w === 1'b1);

  cycle_start();
  enum_in = {TWO, ONE, ZERO};

  cycle_end();
  assert(enum_total_31w === 1'b1);

  end
endmodule

