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
// Description: Testbench for prim_secded modules

module tb_ecc_secded #(
  parameter int unsigned DataWidth = 128 // 8, 16, 32, 64, 128
);

  localparam int unsigned RunCycles = 100000;
  localparam int unsigned ProtectBits = $clog2(DataWidth)+2;

  /******************
   *  Helper tasks  *
   ******************/

  localparam time         TTest     = 8ns;
  localparam time         TApply    = 2ns;

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

  // Data type
  typedef logic [            DataWidth-1:0] data_t;
  typedef logic [DataWidth+ProtectBits-1:0] prot_t;
  typedef logic [          ProtectBits-1:0] synd_t;

  class stimuli_t;
    rand data_t in;
    prot_t inject;

    rand int error_pos_1;
    rand int error_pos_2;

    function prot_t get_inject;
      inject = '0;
      if (error_pos_1 < DataWidth+ProtectBits)
        inject[error_pos_1] = 1'b1;
      if (error_pos_2 < DataWidth+ProtectBits)
        inject[error_pos_2] = 1'b1;
      return inject;
    endfunction : get_inject

    constraint no_error {error_pos_1 > DataWidth+ProtectBits; error_pos_2 > DataWidth+ProtectBits;}
    constraint single_error {error_pos_1 < DataWidth+ProtectBits; error_pos_2 > DataWidth+ProtectBits;}
    constraint double_error {error_pos_1 < DataWidth+ProtectBits; error_pos_2 < DataWidth+ProtectBits; error_pos_1 != error_pos_2;}
  endclass : stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    data_t out;
    synd_t syndrome, syndrome_corrector, syndrome_corrector_decoder;
    logic [1:0] error, error_corrector, error_correcter_decoder;
  } result_t;
  result_t golden_queue[$];

  function automatic void generate_stimuli();
    // Step 1: No injected errors
    repeat(1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;
        automatic result_t result;

        // Activate constraints
        stimuli.no_error.constraint_mode(1);
        stimuli.single_error.constraint_mode(0);
        stimuli.double_error.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          result = '{out: stimuli.in,
                                   syndrome: {ProtectBits{1'b0}}, error: 2'b00,
                                   syndrome_corrector: {ProtectBits{1'b0}}, error_corrector: 2'b00,
                                   syndrome_corrector_decoder: {ProtectBits{1'b0}}, error_correcter_decoder: 2'b00};
          golden_queue.push_back(result);
        end else begin
          $error("Could not randomize.");
        end
      end

    // Step 2: Single error
    repeat(1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;
        automatic result_t result;

        // Activate constraints
        stimuli.no_error.constraint_mode(0);
        stimuli.single_error.constraint_mode(1);
        stimuli.double_error.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          result = '{out: stimuli.in,
                                   syndrome: {ProtectBits{1'b?}}, error: 2'b01,
                                   syndrome_corrector: {ProtectBits{1'b?}}, error_corrector: 2'b01,
                                   syndrome_corrector_decoder: {ProtectBits{1'b0}}, error_correcter_decoder: 2'b00};
          golden_queue.push_back(result);
        end else begin
          $error("Could not randomize.");
        end
      end

    // Step 3: Double error
    repeat(1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;
        automatic result_t result;

        // Activate constraints
        stimuli.no_error.constraint_mode(0);
        stimuli.single_error.constraint_mode(0);
        stimuli.double_error.constraint_mode(1);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          result = '{out: {DataWidth{1'b?}},
                                   syndrome: {ProtectBits{1'b?}}, error: 2'b10,
                                   syndrome_corrector: {ProtectBits{1'b?}}, error_corrector: 2'b10,
                                   syndrome_corrector_decoder: {ProtectBits{1'b?}}, error_correcter_decoder: 2'b??};
          golden_queue.push_back(result);
        end else begin
          $error("Could not randomize.");
        end
      end
  endfunction : generate_stimuli

  // Apply stimuli
  data_t in;
  prot_t inject;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);

    stimuli = stimuli_queue.pop_front();
    in = stimuli.in;
    inject = stimuli.get_inject();
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
  //       |__________|   |__________|  | |__________|
  //                                    |
  //                                    |  ___________      __________
  //                                    | |           |    |          |
  //                                    ->|  CORRECT  | -->|  DECODE  | --> out_corrected
  //                                      |___________|    |__________|
  //

  data_t out, out_corrected;
  synd_t syndrome, syndrome_corrector, syndrome_corrector_decoder;
  prot_t prot_out, prot_in, prot_corrected;
  logic [1:0] error, error_corrector, error_correcter_decoder;

  hsiao_ecc_enc #(
    .DataWidth(DataWidth),
    .ProtWidth (ProtectBits),
    .PrintHsiao(1'b1)
  ) i_dut_encode (
    .in (in),
    .out(prot_out)
  );

  assign prot_in = prot_out ^ inject;

  hsiao_ecc_dec #(
    .DataWidth(DataWidth),
    .ProtWidth (ProtectBits),
    .PrintHsiao(1'b1)
  ) i_dut_decode (
    .in        (prot_in),
    .out       (out),
    .syndrome_o(syndrome),
    .err_o     (error)
  );

  hsiao_ecc_cor #(
    .DataWidth(DataWidth),
    .ProtWidth (ProtectBits),
    .PrintHsiao(1'b1)
  ) i_dut_correct (
    .in        (prot_in),
    .out       (prot_corrected),
    .syndrome_o(syndrome_corrector),
    .err_o     (error_corrector)
  );

  hsiao_ecc_dec #(
    .DataWidth(DataWidth),
    .ProtWidth (ProtectBits),
    .PrintHsiao(1'b1)
  ) i_dut_correct_decode (
    .in        (prot_corrected),
    .out       (out_corrected),
    .syndrome_o(syndrome_corrector_decoder),
    .err_o     (error_correcter_decoder)
  );

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  function automatic void collect_result;
    automatic result_t result;
    result = '{out: out,
                             syndrome: syndrome,
                             error: error,
                             syndrome_corrector: syndrome_corrector,
                             error_corrector: error_corrector,
                             syndrome_corrector_decoder: syndrome_corrector_decoder,
                             error_correcter_decoder: error_correcter_decoder};
    result_queue.push_back(result);
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

    $display("Testing data width %0d.", DataWidth);

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
