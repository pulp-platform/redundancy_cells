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

  /**********************
   *  DUTs              *
   **********************/

  `VOTE31 (in, out_31);
  `VOTE31F(in, out_31f, fail_31f);
  `VOTE31W(in, out_31w, where_31w, total_31w);

  `VOTE33 (in, out_33);
  `VOTE33F(in, out_33f, fail_33f);
  `VOTE33W(in, out_33w, where_33w, total_33w);

  // The same thing but with enums to ensure macros run fine with those
  `VOTE31 (enum_in, enum_out_31);
  `VOTE31F(enum_in, enum_out_31f, enum_fail_31f);
  `VOTE31W(enum_in, enum_out_31w, enum_where_31w, enum_total_31w);

  `VOTE33 (enum_in, enum_out_33);
  `VOTE33F(enum_in, enum_out_33f, enum_fail_33f);
  `VOTE33W(enum_in, enum_out_33w, enum_where_33w, enum_total_33w);

  initial begin
    cycle_start();
    in = 3'b000;
    enum_in = {ZERO, ZERO, ZERO};

    cycle_end();
    assert(out_31         == 1'b0);
    assert(out_31f        == 1'b0);
    assert(out_31w        == 1'b0);

    assert(enum_out_31    == ZERO);
    assert(enum_out_31f   == ZERO);
    assert(enum_out_31w   == ZERO);

    assert(out_33   == 3'b000);
    assert(out_33f  == 3'b000);
    assert(out_33w  == 3'b000);

    assert(enum_out_33   == {ZERO, ZERO, ZERO});
    assert(enum_out_33f  == {ZERO, ZERO, ZERO});
    assert(enum_out_33w  == {ZERO, ZERO, ZERO});

    assert(fail_31f       == 1'b0);
    assert(enum_fail_31f  == 1'b0);
    assert(fail_33f       == 1'b0);
    assert(enum_fail_33f  == 1'b0);

    assert(where_31w      == 3'b000);
    assert(enum_where_31w == 3'b000);
    assert(where_33w      == 3'b000);
    assert(enum_where_33w == 3'b000);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);

    cycle_start();
    in = 3'b001;
    enum_in = {ZERO, ZERO, ONE};

    cycle_end();
    assert(out_31         == 1'b0);
    assert(out_31f        == 1'b0);
    assert(out_31w        == 1'b0);

    assert(enum_out_31    == ZERO);
    assert(enum_out_31f   == ZERO);
    assert(enum_out_31w   == ZERO);

    assert(out_33   == 3'b000);
    assert(out_33f  == 3'b000);
    assert(out_33w  == 3'b000);

    assert(enum_out_33   == {ZERO, ZERO, ZERO});
    assert(enum_out_33f  == {ZERO, ZERO, ZERO});
    assert(enum_out_33w  == {ZERO, ZERO, ZERO});

    assert(fail_31f       == 1'b1);
    assert(enum_fail_31f  == 1'b1);
    assert(fail_33f       == 1'b1);
    assert(enum_fail_33f  == 1'b1);

    assert(where_31w      == 3'b001);
    assert(enum_where_31w == 3'b001);
    assert(where_33w      == 3'b001);
    assert(enum_where_33w == 3'b001);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);


    cycle_start();
    in = 3'b010;
    enum_in = {ZERO, ONE, ZERO};

    cycle_end();
    assert(out_31         == 1'b0);
    assert(out_31f        == 1'b0);
    assert(out_31w        == 1'b0);

    assert(enum_out_31    == ZERO);
    assert(enum_out_31f   == ZERO);
    assert(enum_out_31w   == ZERO);

    assert(out_33   == 3'b000);
    assert(out_33f  == 3'b000);
    assert(out_33w  == 3'b000);

    assert(enum_out_33   == {ZERO, ZERO, ZERO});
    assert(enum_out_33f  == {ZERO, ZERO, ZERO});
    assert(enum_out_33w  == {ZERO, ZERO, ZERO});

    assert(fail_31f       == 1'b1);
    assert(enum_fail_31f  == 1'b1);
    assert(fail_33f       == 1'b1);
    assert(enum_fail_33f  == 1'b1);

    assert(where_31w      == 3'b010);
    assert(enum_where_31w == 3'b010);
    assert(where_33w      == 3'b010);
    assert(enum_where_33w == 3'b010);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);

    cycle_start();
    in = 3'b100;
    enum_in = {ONE, ZERO, ZERO};

    cycle_end();
    assert(out_31         == 1'b0);
    assert(out_31f        == 1'b0);
    assert(out_31w        == 1'b0);

    assert(enum_out_31    == ZERO);
    assert(enum_out_31f   == ZERO);
    assert(enum_out_31w   == ZERO);

    assert(out_33   == 3'b000);
    assert(out_33f  == 3'b000);
    assert(out_33w  == 3'b000);

    assert(enum_out_33   == {ZERO, ZERO, ZERO});
    assert(enum_out_33f  == {ZERO, ZERO, ZERO});
    assert(enum_out_33w  == {ZERO, ZERO, ZERO});

    assert(fail_31f       == 1'b1);
    assert(enum_fail_31f  == 1'b1);
    assert(fail_33f       == 1'b1);
    assert(enum_fail_33f  == 1'b1);

    assert(where_31w      == 3'b100);
    assert(enum_where_31w == 3'b100);
    assert(where_33w      == 3'b100);
    assert(enum_where_33w == 3'b100);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);

    cycle_start();
    in = 3'b111;
    enum_in = {ONE, ONE, ONE};

    cycle_end();
    assert(out_31         == 1'b1);
    assert(out_31f        == 1'b1);
    assert(out_31w        == 1'b1);

    assert(enum_out_31    == ONE);
    assert(enum_out_31f   == ONE);
    assert(enum_out_31w   == ONE);

    assert(out_33   == 3'b111);
    assert(out_33f  == 3'b111);
    assert(out_33w  == 3'b111);

    assert(enum_out_33   == {ONE, ONE, ONE});
    assert(enum_out_33f  == {ONE, ONE, ONE});
    assert(enum_out_33w  == {ONE, ONE, ONE});

    assert(fail_31f       == 1'b0);
    assert(enum_fail_31f  == 1'b0);
    assert(fail_33f       == 1'b0);
    assert(enum_fail_33f  == 1'b0);

    assert(where_31w      == 3'b000);
    assert(enum_where_31w == 3'b000);
    assert(where_33w      == 3'b000);
    assert(enum_where_33w == 3'b000);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);

    cycle_start();
    in = 3'b110;
    enum_in = {ONE, ONE, ZERO};

    cycle_end();
    assert(out_31         == 1'b1);
    assert(out_31f        == 1'b1);
    assert(out_31w        == 1'b1);

    assert(enum_out_31    == ONE);
    assert(enum_out_31f   == ONE);
    assert(enum_out_31w   == ONE);

    assert(out_33   == 3'b111);
    assert(out_33f  == 3'b111);
    assert(out_33w  == 3'b111);

    assert(enum_out_33   == {ONE, ONE, ONE});
    assert(enum_out_33f  == {ONE, ONE, ONE});
    assert(enum_out_33w  == {ONE, ONE, ONE});

    assert(fail_31f       == 1'b1);
    assert(enum_fail_31f  == 1'b1);
    assert(fail_33f       == 1'b1);
    assert(enum_fail_33f  == 1'b1);

    assert(where_31w      == 3'b001);
    assert(enum_where_31w == 3'b001);
    assert(where_33w      == 3'b001);
    assert(enum_where_33w == 3'b001);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);

    cycle_start();
    in = 3'b101;
    enum_in = {ONE, ZERO, ONE};

    cycle_end();
    assert(out_31         == 1'b1);
    assert(out_31f        == 1'b1);
    assert(out_31w        == 1'b1);

    assert(enum_out_31    == ONE);
    assert(enum_out_31f   == ONE);
    assert(enum_out_31w   == ONE);

    assert(out_33   == 3'b111);
    assert(out_33f  == 3'b111);
    assert(out_33w  == 3'b111);

    assert(enum_out_33   == {ONE, ONE, ONE});
    assert(enum_out_33f  == {ONE, ONE, ONE});
    assert(enum_out_33w  == {ONE, ONE, ONE});

    assert(fail_31f       == 1'b1);
    assert(enum_fail_31f  == 1'b1)
    assert(fail_33f       == 1'b1);;
    assert(enum_fail_33f  == 1'b1);

    assert(where_31w      == 3'b010);
    assert(enum_where_31w == 3'b010);
    assert(where_33w      == 3'b010);
    assert(enum_where_33w == 3'b010);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);

    cycle_start();
    in = 3'b011;
    enum_in = {ZERO, ONE, ONE};

    cycle_end();
    assert(out_31         == 1'b1);
    assert(out_31f        == 1'b1);
    assert(out_31w        == 1'b1);

    assert(enum_out_31    == ONE);
    assert(enum_out_31f   == ONE);
    assert(enum_out_31w   == ONE);

    assert(out_33   == 3'b111);
    assert(out_33f  == 3'b111);
    assert(out_33w  == 3'b111);

    assert(enum_out_33   == {ONE, ONE, ONE});
    assert(enum_out_33f  == {ONE, ONE, ONE});
    assert(enum_out_33w  == {ONE, ONE, ONE});

    assert(fail_31f       == 1'b1);
    assert(enum_fail_31f  == 1'b1);
    assert(fail_33f       == 1'b1);
    assert(enum_fail_33f  == 1'b1);

    assert(where_31w      == 3'b100);
    assert(enum_where_31w == 3'b100);
    assert(where_33w      == 3'b100);
    assert(enum_where_33w == 3'b100);

    assert(total_31w      == 1'b0);
    assert(enum_total_31w == 1'b0);
    assert(total_33w      == 1'b0);
    assert(enum_total_33w == 1'b0);


  // Check that the total fault works
  cycle_start();
  enum_in = {ZERO, ONE, TWO};

  cycle_end();
  assert(enum_total_31w == 1'b1);
  assert(enum_total_33w == 1'b1);

  cycle_start();
  enum_in = {ZERO, TWO, ONE};

  cycle_end();
  assert(enum_total_31w == 1'b1);
  assert(enum_total_33w == 1'b1);

  cycle_start();
  enum_in = {ONE, ZERO, TWO};

  cycle_end();
  assert(enum_total_31w == 1'b1);
  assert(enum_total_33w == 1'b1);

  cycle_start();
  enum_in = {ONE, TWO, ZERO};

  cycle_end();
  assert(enum_total_31w == 1'b1);
  assert(enum_total_33w == 1'b1);

  cycle_start();
  enum_in = {TWO, ZERO, ONE};

  cycle_end();
  assert(enum_total_31w == 1'b1);
  assert(enum_total_33w == 1'b1);


  cycle_start();
  enum_in = {TWO, ONE, ZERO};

  cycle_end();
  assert(enum_total_31w == 1'b1);
  assert(enum_total_33w == 1'b1);

  end
endmodule

