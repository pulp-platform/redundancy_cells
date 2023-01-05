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
// Description: Testbench for the tmr register module
// Note: This testbench may only be run with the fault injection script running concurrently

module tb_tmr_reg #(
  parameter int unsigned DataWidth = 32,
  // FF Settings
  parameter bit HasReset = 1,
  parameter bit AsynchronousReset = 1,
  parameter bit ActiveLowReset = 1,
  parameter bit HasLoad = 0,
  // Testbench Settings
  parameter int unsigned RunCycles = 100
) ();

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

  logic clk;
  logic rst_n;

  clk_rst_gen #(
    .ClkPeriod    ( TTest + TApply ),
    .RstClkCycles ( 5              )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  /************************
   *  Stimuli generation  *
   ************************/

  // Data type
  typedef logic [  DataWidth-1:0] data_t;
  typedef logic [3*DataWidth-1:0] prot_t;

  class stimuli_t;
    // stimuli settings
    bit inject_fault;

    // randomized inputs
    rand data_t in;
    rand data_t flip;
    rand int flip_pos [DataWidth];

    // final injection
    prot_t inject;

    constraint flip_bits {
      if(inject_fault) {
        flip != 0;
      } else {
        flip == 0;
      }
    };

    constraint flip_position { foreach (flip_pos[i]) {flip_pos[i] inside {0, 1, 2};}}

    function void post_randomize();
      inject = '0;
      foreach (flip_pos[i]) begin
        inject[DataWidth*flip_pos[i]+i] = flip[i];
      end
    endfunction

  endclass : stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    data_t out;
    logic error;
  } result_t;
  result_t golden_queue[$];

  function automatic void generate_stimuli();
    // No valid output in the first cycle
    golden_queue.push_back('{out: {DataWidth{1'b?}}, error: 1'b?});

    // Step 1: No injected errors
    for (int i = 0; i < RunCycles; i++) begin
      automatic stimuli_t stimuli = new;
      stimuli.inject_fault = 1'b0;

      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");

      stimuli_queue.push_back(stimuli);
      golden_queue.push_back('{out: stimuli.in, error: 1'b0});
    end

    // Step 2: Correctable Error
    for (int i = 0; i < RunCycles; i++) begin
      // Stimuli with fault
      automatic stimuli_t stimuli = new;
      stimuli.inject_fault = 1'b1;

      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");

      stimuli_queue.push_back(stimuli);
      golden_queue.push_back('{out: stimuli.in, error: 1'b1});
    end
  endfunction : generate_stimuli

  // Apply stimuli
  data_t in;
  prot_t fault_mask_next, fault_mask, inject_val;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);

    stimuli = stimuli_queue.pop_front();
    in = stimuli.in;
    fault_mask_next = stimuli.inject;
  endtask : apply_stimuli

  initial begin : init_stimuli
    in = '0;
    fault_mask_next = '0;
  end : init_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  data_t out;
  logic error;

  tmr_reg #(
    .DataWidth         ( DataWidth         ),
    .HasReset          ( HasReset          ),
    .AsynchronousReset ( AsynchronousReset ),
    .ActiveLowReset    ( ActiveLowReset    ),
    .HasLoad           ( HasLoad           )
  ) i_dut (
    .clk_i         ( clk   ),
    .rst_ni        ( rst_n ),
    .data_i        ( in    ),
    .data_o        ( out   ),
    .err_o         ( error ),
    .reset_value_i ( '0    ),
    .load_en_i     ( '0    )
);

  always_ff @( posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fault_mask <= '0;
    end else begin
      fault_mask <= fault_mask_next;
    end
  end

  // 'inject_val' is read by the fault injection script and is injected into 'i_dut.data_q'
  assign inject_val = fault_mask ^ i_dut.data_q;

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  function automatic void collect_result;
    result_queue.push_back('{out: out, error: error});
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

  assign num_errors_o = error_cnt;

  initial begin: tb

    $display("Generating Stimuli");

    @(posedge rst_n)

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

    $display("Found %d Errors in %d tests.", error_cnt, test_cnt);
    $finish(0);

  end: tb

endmodule
