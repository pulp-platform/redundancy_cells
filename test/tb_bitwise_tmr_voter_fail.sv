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
// Testbench for bitwise TMR Word Voter with Failure Output

module tb_bitwise_tmr_voter_fail;

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
    rand data_t a_i;
    rand data_t b_i;
    rand data_t c_i;

    constraint equal_inputs { a_i == b_i; a_i == c_i; }
    constraint a_i_different { a_i != b_i; b_i == c_i; }
    constraint b_i_different { b_i != a_i; a_i == c_i; }
    constraint c_i_different { c_i != a_i; a_i == b_i; }
    constraint all_different { a_i != b_i; a_i != c_i; b_i != c_i; }
  endclass: stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    data_t majority_o;
    logic fault_detected_o;
  } result_t;

  result_t golden_queue[$];

  function automatic void generate_stimuli();
    // Step 1: Three equal values
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(1);
        stimuli.a_i_different.constraint_mode(0);
        stimuli.b_i_different.constraint_mode(0);
        stimuli.c_i_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{majority_o: stimuli.a_i, fault_detected_o: 1'b0});
        end else
          $error("Could not randomize.");
      end

    // Step 2: a_i is different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.a_i_different.constraint_mode(1);
        stimuli.b_i_different.constraint_mode(0);
        stimuli.c_i_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{majority_o: stimuli.b_i, fault_detected_o: 1'b1});
        end else
          $error("Could not randomize.");
      end

    // Step 3: b_i is different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.a_i_different.constraint_mode(0);
        stimuli.b_i_different.constraint_mode(1);
        stimuli.c_i_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{majority_o: stimuli.a_i, fault_detected_o: 1'b1});
        end else
          $error("Could not randomize.");
      end

    // Step 4: c_i is different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.a_i_different.constraint_mode(0);
        stimuli.b_i_different.constraint_mode(0);
        stimuli.c_i_different.constraint_mode(1);
        stimuli.all_different.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{majority_o: stimuli.a_i, fault_detected_o: 1'b1});
        end else
          $error("Could not randomize.");
      end

    // Step 5: all different
    repeat (1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.equal_inputs.constraint_mode(0);
        stimuli.a_i_different.constraint_mode(0);
        stimuli.b_i_different.constraint_mode(0);
        stimuli.c_i_different.constraint_mode(0);
        stimuli.all_different.constraint_mode(1);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{majority_o: {DataWidth{1'b?}}, fault_detected_o: 1'b1});
        end else
          $error("Could not randomize.");
      end
  endfunction: generate_stimuli

  // Apply stimuli
  data_t a_i;
  data_t b_i;
  data_t c_i;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);

    stimuli = stimuli_queue.pop_front();
    a_i    = stimuli.a_i;
    b_i    = stimuli.b_i;
    c_i    = stimuli.c_i;
  endtask: apply_stimuli

  initial begin: init_stimuli
    a_i = '0;
    b_i = '0;
    c_i = '0;
  end: init_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  data_t       majority_o;
  logic        fault_detected_o;

  bitwise_TMR_voter_fail #(
    .DataWidth(DataWidth),
    .VoterType(2        )
  ) i_dut (
    .a_i              ( a_i              ),
    .b_i              ( b_i              ),
    .c_i              ( c_i              ),
    .majority_o       ( majority_o       ),
    .fault_detected_o ( fault_detected_o )
  );

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  longint error_cnt;

  function automatic void collect_result;
    result_queue.push_back('{majority_o: majority_o, fault_detected_o: fault_detected_o});
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

