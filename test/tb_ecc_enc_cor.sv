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
// Description: Testbench for ecc encode and decode modules
// Use the 'tb_ecc_enc_dec_multi' below to run multiple test simultaneously.

`include "ECC_reg/ecc_calc.svh"

module tb_ecc_enc_cor #(
  parameter int unsigned DataWidth = 0,
  // ECC Settings
  parameter int unsigned NumErrorDetect = 2,
  parameter int unsigned NumErrorCorrect = 1,
  // Test settings
  parameter int unsigned RunCycles = 100
) (
  input  logic       enable_i,
  output logic       finished_o,
  output logic[31:0] num_errors_o
);

  // ECC dist and width calculations
  localparam int unsigned EccDist = `ECC_DIST(NumErrorCorrect, NumErrorDetect);
  localparam int          EccWidth = `ECC_WIDTH(DataWidth, EccDist);

  /******************
   *  Helper tasks  *
   ******************/

  localparam time TTest  = 8ns;
  localparam time TApply = 2ns;

  task cycle_start();
    #TApply;
  endtask : cycle_start

  task cycle_end();
    #TTest;
  endtask : cycle_end

  /**********************
   *  Helper variables  *
   **********************/

  longint test_cnt;
  longint error_cnt;

  /************************
   *  Stimuli generation  *
   ************************/

  class stimuli_t;

    // fixed stimuli inputs
    int unsigned num_flips;

    // randomized inputs
    rand logic [         DataWidth-1:0] in;
    rand logic [EccWidth+DataWidth-1:0] inject;

    constraint error_bits {$countones(inject) == num_flips;}

  endclass : stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    logic[DataWidth+EccWidth-1:0] out;
    logic e_cor, e_uncor, e_check;
  } result_t;

  result_t golden_queue [$];

  function automatic void generate_stimuli();

    // Step 1: No injected errors
    for (int i = 0; i < RunCycles; i++) begin
      automatic stimuli_t stimuli = new;

      stimuli.num_flips = 0;

      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");

      stimuli_queue.push_back(stimuli);
      golden_queue.push_back('{out: stimuli.in, e_cor: 1'b0, e_uncor: 1'b0, e_check: 1'b0});
    end

    // Step 2: Correctable Errors
    for (int c = 1; c <= NumErrorCorrect; c++) begin
      for (int i = 0; i < RunCycles; i++) begin
        // Stimuli with fault
        automatic stimuli_t stimuli = new;
        stimuli.num_flips = c;
        if (!stimuli.randomize()) $error("Could not randomize.");

        stimuli_queue.push_back(stimuli);
        golden_queue.push_back('{out: stimuli.in, e_cor: 1'b1, e_uncor: 1'b0, e_check: 1'b0});
      end
    end

    // Step 3: Uncorrectable, Detectable Errors
    for (int c = NumErrorCorrect + 1; c <= NumErrorDetect; c++) begin
      for (int i = 0; i < RunCycles; i++) begin
        // Stimuli with fault
        automatic stimuli_t stimuli = new;
        stimuli.num_flips = c;
        if (!stimuli.randomize()) $error("Could not randomize.");

        stimuli_queue.push_back(stimuli);
        golden_queue.push_back('{out: 'b?, e_cor: 1'b0, e_uncor: 1'b1, e_check: 1'b1});
      end
    end
  endfunction : generate_stimuli

  // Apply stimuli
  logic[         DataWidth-1:0] in;
  logic[EccWidth+DataWidth-1:0] inject;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);

    stimuli = stimuli_queue.pop_front();
    in = stimuli.in;
    inject = stimuli.inject;
  endtask : apply_stimuli

  initial begin : init_stimuli
    in = '0;
    inject = '0;
  end : init_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  //        __________     __________      __________
  //       |          |   |          |    |          |
  // in -->|  ENCODE  |-->|  Inject  | -->|  DECODE  | --> out
  //       |__________|   |__________|    |__________|
  //

  logic[EccWidth+DataWidth-1:0] protect, cor_protec;
  logic[         DataWidth-1:0] out;
  logic e_cor, e_uncor, e_cor_2, e_uncor_2, e_check;

  ecc_enc #(
    .DataWidth       (DataWidth      ),
    .NumErrorDetect  (NumErrorDetect ),
    .NumErrorCorrect (NumErrorCorrect)
  ) i_dut_enc (
    .data_i (in     ),
    .data_o (protect)
  );

  ecc_cor #(
    .DataWidth       (DataWidth      ),
    .NumErrorDetect  (NumErrorDetect ),
    .NumErrorCorrect (NumErrorCorrect)
  ) i_dut_cor (
    .data_i                (protect ^ inject),
    .data_o                (cor_protec      ),
    .error_correctable_o   (e_cor           ),
    .error_uncorrectable_o (e_uncor         )
  );

  ecc_cor #(
    .DataWidth       (DataWidth      ),
    .NumErrorDetect  (NumErrorDetect ),
    .NumErrorCorrect (NumErrorCorrect)
  ) i_dut_cor_check (
    .data_i                (cor_protec      ),
    .data_o                (                ),
    .error_correctable_o   (e_cor_2         ),
    .error_uncorrectable_o (e_uncor_2       )
  );

  assign out = cor_protec[DataWidth-1:0];
  assign e_check = e_cor_2 | e_uncor_2;

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  function automatic void collect_result;
    result_queue.push_back('{out: out, e_cor: e_cor, e_uncor: e_uncor, e_check: e_check});
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
        $warning("ERROR! DataWidth %0d, Test %0d: expected %p, found %p.", DataWidth, test_cnt, golden, result);
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
      if(enable_i) begin
        cycle_start();
        apply_stimuli();
        cycle_end();
        collect_result();
      end
    end
  endtask : run

  assign num_errors_o = error_cnt;

  initial begin: tb
    // Initialize variables
    test_cnt  = '0;
    error_cnt = '0;
    finished_o = '0;

    wait(enable_i);

    $display("Generating Stimuli for Datawidth %d", DataWidth);

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

    finished_o = 1'b1;
  end: tb

endmodule

module tb_ecc_enc_cor_multi #(
  parameter int unsigned MaxDataWidth = 0,
  // ECC Settings
  parameter int unsigned NumErrorDetect = 2,
  parameter int unsigned NumErrorCorrect = 1,
  // Testbench parameters
  parameter int unsigned RunCycles = 500
);
  localparam int unsigned NumTests = RunCycles * MaxDataWidth * ((NumErrorDetect > NumErrorCorrect) ? NumErrorDetect : NumErrorCorrect);

  logic                         enable;
  logic[MaxDataWidth-1:0]       finished;
  logic[MaxDataWidth-1:0][31:0] error_cnt;

  for(genvar datawidth = 1; datawidth <= MaxDataWidth; datawidth++) begin : gen_dut
    tb_ecc_enc_cor #(
      .DataWidth       (datawidth      ),
      .NumErrorDetect  (NumErrorDetect ),
      .NumErrorCorrect (NumErrorCorrect),
      .RunCycles       (RunCycles      )
    ) i_dut (
      .enable_i     (enable                ),
      .finished_o   (finished[datawidth-1] ),
      .num_errors_o (error_cnt[datawidth-1])
    );
  end

  longint total_errors;

  initial begin
    $display("Testing With Parameters:");
    $display(" - MaxDataWidth:    %30d", MaxDataWidth);
    $display(" - NumErrorDetect:  %30d", NumErrorDetect);
    $display(" - NumErrorCorrect: %30d", NumErrorCorrect);

    enable = 1'b1;

    wait( finished == {MaxDataWidth{1'b1}} );

    total_errors = '0;

    $display("Testing Completed:");
    for(int i = 0; i < MaxDataWidth; i++) begin
      $display("Datawidth %d: %d Errors.", i+1, error_cnt[i]);
      total_errors += error_cnt[i];
    end

    $display("Finished Running %d tests over %d DataWidths", NumTests, MaxDataWidth);
    $display("Errors: %d", total_errors);

    $finish(0);

  end

endmodule
