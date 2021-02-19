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
// Testbench for bitwise TMR Word Voter

module tb_bitwise_tmr_voter_test;

  localparam int unsigned RunCycles = 100000;
  localparam int unsigned DataWidth = 32;

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

  /************************
   *  Stimuli generation  *
   ************************/

  // Data type
  typedef logic [DataWidth-1:0] data_t;

  class stimuli_t;
    rand data_t in_a;
    rand data_t in_b;
    rand data_t in_c;

    constraint equal_inputs { in_a == in_b; in_a == in_c; }
    constraint in_a_different { in_a != in_b; in_b == in_c; }
    constraint in_b_different { in_b != in_a; in_a == in_c; }
    constraint in_c_different { in_c != in_a; in_a == in_b; }
    constraint all_different { in_a != in_b; in_a != in_c; in_b != in_c; }
  endclass: stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    data_t out;
    logic error;
    logic [2:0] error_cba;
  } result_t;
  result_t golden_queue[$];

  function automatic void generate_stimuli();
    // Step 1: Three equal values
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(1);
        stimuli.in_a_different.constraint_mode(0);
        stimuli.in_b_different.constraint_mode(0);
        stimuli.in_c_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: stimuli.in_a, error: 1'b0, error_cba: 3'b000});
        end else
          $error("Could not randomize.");
      end

    // Step 2: in_a is different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.in_a_different.constraint_mode(1);
        stimuli.in_b_different.constraint_mode(0);
        stimuli.in_c_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: stimuli.in_b, error: 1'b0, error_cba: 3'b001});
        end else
          $error("Could not randomize.");
      end

    // Step 3: in_b is different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.in_a_different.constraint_mode(0);
        stimuli.in_b_different.constraint_mode(1);
        stimuli.in_c_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: stimuli.in_a, error: 1'b0, error_cba: 3'b010});
        end else
          $error("Could not randomize.");
      end

    // Step 4: in_c is different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.in_a_different.constraint_mode(0);
        stimuli.in_b_different.constraint_mode(0);
        stimuli.in_c_different.constraint_mode(1);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: stimuli.in_a, error: 1'b0, error_cba: 3'b100});
        end else
          $error("Could not randomize.");
      end

    // Step 5: all different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.in_a_different.constraint_mode(0);
        stimuli.in_b_different.constraint_mode(0);
        stimuli.in_c_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(1);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: {DataWidth{1'b?}}, error: 1'b1, error_cba: 3'b???});
        end else
          $error("Could not randomize.");
      end
  endfunction: generate_stimuli

  // Apply stimuli
  data_t in_a;
  data_t in_b;
  data_t in_c;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);

    stimuli = stimuli_queue.pop_front();
    in_a    = stimuli.in_a;
    in_b    = stimuli.in_b;
    in_c    = stimuli.in_c;
  endtask: apply_stimuli

  initial begin: init_stimuli
    in_a = '0;
    in_b = '0;
    in_c = '0;
  end: init_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  data_t       out;
  logic        error;
  logic  [2:0] error_cba;

  bitwise_TMR_voter #(
    .DataWidth(DataWidth),
    .VoterType(2        )
  ) dut (
    .in_a      ( in_a      ),
    .in_b      ( in_b      ),
    .in_c      ( in_c      ),
    .out       ( out       ),
    .error     ( error     ),
    .error_cba ( error_cba )
  );

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  longint error_cnt;

  function automatic void collect_result;
    result_queue.push_back('{out: out, error: error, error_cba: error_cba});
  endfunction: collect_result

  task automatic check_result;
    automatic result_t result;
    automatic result_t golden;

    do begin
      wait(result_queue.size() != 0);

      // Capture the results
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // Account for this check
      test_cnt++;

      if (result != golden) begin
        $warning("ERROR! Test %0d: expected %p, found %p.", test_cnt, golden, result);
        error_cnt++;
      end
    end while (stimuli_queue.size() != 0);
  endtask: check_result

  /****************
   *  Test bench  *
   ****************/

  task run();
    // Apply stimuli and collect results cycle
    forever begin
      cycle_start();
      apply_stimuli();
      cycle_end();
      collect_result();
    end
  endtask : run

  initial begin: tb
    // Initialize variables
    test_cnt  = '0;
    error_cnt = '0;

    fork
      // Run the TB
      run();
      fork
        // Generate stimuli
        generate_stimuli();
        // Check result
        check_result();
      join
    join_any

    $display("Checked %0d tests, found %0d mismatches.", test_cnt, error_cnt);
    $finish(error_cnt);
  end: tb

endmodule

