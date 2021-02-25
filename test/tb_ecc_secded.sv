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
      if (error_pos_1 < DataWidth)
        inject[error_pos_1] = 1'b1;
      if (error_pos_2 < DataWidth)
        inject[error_pos_2] = 1'b1;
      return inject;
    endfunction : get_inject

    constraint no_error {error_pos_1 > DataWidth; error_pos_2 > DataWidth;}
    constraint single_error {error_pos_1 < DataWidth; error_pos_2 > DataWidth;}
    constraint double_error {error_pos_1 < DataWidth; error_pos_2 < DataWidth; error_pos_1 != error_pos_2;}
  endclass : stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    data_t out;
    synd_t syndrome;
    logic [1:0] error;
  } result_t;
  result_t golden_queue[$];

  function automatic void generate_stimuli();
    // Step 1: No injected errors
    repeat(1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.no_error.constraint_mode(1);
        stimuli.single_error.constraint_mode(0);
        stimuli.double_error.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: stimuli.in, syndrome: {ProtectBits{1'b0}}, error: 2'b00});
        end else begin
          $error("Could not randomize.");
        end
      end

    // Step 2: Single error
    repeat(1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.no_error.constraint_mode(0);
        stimuli.single_error.constraint_mode(1);
        stimuli.double_error.constraint_mode(0);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: stimuli.in, syndrome: {ProtectBits{1'b?}}, error: 2'b01});
        end else begin
          $error("Could not randomize.");
        end
      end

    // Step 3: Double error
    repeat(1)
      for (int i = 0; i < RunCycles; i++) begin
        automatic stimuli_t stimuli = new;

        // Activate constraints
        stimuli.no_error.constraint_mode(0);
        stimuli.single_error.constraint_mode(0);
        stimuli.double_error.constraint_mode(1);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{out: {DataWidth{1'b?}}, syndrome: {ProtectBits{1'b?}}, error: 2'b10});
        end else begin
          $error("Could not randomize.");
        end
      end
  endfunction : generate_stimuli

  // Apply stimuli
  data_t in;
  data_t inject;

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

  data_t out;
  synd_t syndrome;
  prot_t prot_out, prot_in;
  logic [1:0] error;

  if (DataWidth == 8) begin
    prim_secded_13_8_enc i_dut_encode (
      .in (in),
      .out(prot_out)
    );
    assign prot_in = prot_out ^ inject;
    prim_secded_13_8_dec i_dut_decode (
      .in        (prot_in),
      .d_o       (out),
      .syndrome_o(syndrome),
      .err_o     (error)
    );
  end else if (DataWidth == 16) begin
    prim_secded_22_16_enc i_dut_encode (
      .in (in),
      .out(prot_out)
    );
    assign prot_in = prot_out ^ inject;
    prim_secded_22_16_dec i_dut_decode (
      .in        (prot_in),
      .d_o       (out),
      .syndrome_o(syndrome),
      .err_o     (error)
    );
  end else if (DataWidth == 32) begin
    prim_secded_39_32_enc i_dut_encode (
      .in (in),
      .out(prot_out)
    );
    assign prot_in = prot_out ^ inject;
    prim_secded_39_32_dec i_dut_decode (
      .in        (prot_in),
      .d_o       (out),
      .syndrome_o(syndrome),
      .err_o     (error)
    );
  end else if (DataWidth == 64) begin
    prim_secded_72_64_enc i_dut_encode (
      .in (in),
      .out(prot_out)
    );
    assign prot_in = prot_out ^ inject;
    prim_secded_72_64_dec i_dut_decode (
      .in        (prot_in),
      .d_o       (out),
      .syndrome_o(syndrome),
      .err_o     (error)
    );
  end else if (DataWidth == 128) begin
    prim_secded_137_128_enc i_dut_encode (
      .in (in),
      .out(prot_out)
    );
    assign prot_in = prot_out ^ inject;
    prim_secded_137_128_dec i_dut_decode (
      .in        (prot_in),
      .d_o       (out),
      .syndrome_o(syndrome),
      .err_o     (error)
    );
  end

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  function automatic void collect_result;
    result_queue.push_back('{out: out, syndrome: syndrome, error: error});
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
