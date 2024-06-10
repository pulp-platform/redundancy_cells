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
// Testbench for TMR Voter with fault output

module tb_tmr_voter_fail;

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

  longint test_cnt;

  logic [2:0] in;
  logic       out_classic, out_kp, out_bn;
  logic       fault_classic, fault_kp, fault_bn;

  TMR_voter_fail #(
    .VoterType(0)
  ) i_dut_classic (
    .a_i              ( in[0]         ),
    .b_i              ( in[1]         ),
    .c_i              ( in[2]         ),
    .majority_o       ( out_classic   ),
    .fault_detected_o ( fault_classic )
  );

  TMR_voter_fail #(
    .VoterType(1)
  ) i_dut_kp (
    .a_i              ( in[0]    ),
    .b_i              ( in[1]    ),
    .c_i              ( in[2]    ),
    .majority_o       ( out_kp   ),
    .fault_detected_o ( fault_kp )
  );

  TMR_voter_fail #(
    .VoterType(2)
  ) i_dut_bn (
    .a_i              ( in[0]    ),
    .b_i              ( in[1]    ),
    .c_i              ( in[2]    ),
    .majority_o       ( out_bn   ),
    .fault_detected_o ( fault_bn )
  );

  initial begin
    cycle_start();
    in = 3'b000;
    cycle_end();
    assert(out_classic   == 1'b0);
    assert(out_kp        == 1'b0);
    assert(out_bn        == 1'b0);
    assert(fault_classic == 1'b0);
    assert(fault_kp      == 1'b0);
    assert(fault_bn      == 1'b0);
    cycle_start();
    in = 3'b001;
    cycle_end();
    assert(out_classic   == 1'b0);
    assert(out_kp        == 1'b0);
    assert(out_bn        == 1'b0);
    assert(fault_classic == 1'b1);
    assert(fault_kp      == 1'b1);
    assert(fault_bn      == 1'b1);
    cycle_start();
    in = 3'b010;
    cycle_end();
    assert(out_classic   == 1'b0);
    assert(out_kp        == 1'b0);
    assert(out_bn        == 1'b0);
    assert(fault_classic == 1'b1);
    assert(fault_kp      == 1'b1);
    assert(fault_bn      == 1'b1);
    cycle_start();
    in = 3'b100;
    cycle_end();
    assert(out_classic   == 1'b0);
    assert(out_kp        == 1'b0);
    assert(out_bn        == 1'b0);
    assert(fault_classic == 1'b1);
    assert(fault_kp      == 1'b1);
    assert(fault_bn      == 1'b1);

    cycle_start();
    in = 3'b111;
    cycle_end();
    assert(out_classic   == 1'b1);
    assert(out_kp        == 1'b1);
    assert(out_bn        == 1'b1);
    assert(fault_classic == 1'b0);
    assert(fault_kp      == 1'b0);
    assert(fault_bn      == 1'b0);
    cycle_start();
    in = 3'b110;
    cycle_end();
    assert(out_classic   == 1'b1);
    assert(out_kp        == 1'b1);
    assert(out_bn        == 1'b1);
    assert(fault_classic == 1'b1);
    assert(fault_kp      == 1'b1);
    assert(fault_bn      == 1'b1);
    cycle_start();
    in = 3'b101;
    cycle_end();
    assert(out_classic   == 1'b1);
    assert(out_kp        == 1'b1);
    assert(out_bn        == 1'b1);
    assert(fault_classic == 1'b1);
    assert(fault_kp      == 1'b1);
    assert(fault_bn      == 1'b1);
    cycle_start();
    in = 3'b011;
    cycle_end();
    assert(out_classic   == 1'b1);
    assert(out_kp        == 1'b1);
    assert(out_bn        == 1'b1);
    assert(fault_classic == 1'b1);
    assert(fault_kp      == 1'b1);
    assert(fault_bn      == 1'b1);
  end

endmodule

