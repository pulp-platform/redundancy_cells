// Copyright 2023 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Rufer <lrufer@student.ethz.ch>

module tb_dmr_handshake_join;

  // Time Settings
  timeunit      1ns;
  timeprecision 1ps;

  // Number of outputs
  localparam int NUM_IN    = 2;
  localparam int DATA_BITS = 16;

  /**********************
   *  Clock and Timing  *
   **********************/

  // Timing parameters
  localparam ClockPeriod = 1ns;
  localparam TApply      = 0.2ns;
  localparam TTest       = 0.8ns;

  // clock and reset
  logic clk;
  logic rst_n;

  // Clock
  always #(ClockPeriod/2) clk = !clk;

  // Reset
  initial begin
    clk   = 1'b1;
    rst_n = 1'b0;
    repeat (5)
      #(ClockPeriod);
    rst_n = 1'b1;
  end

  /************************
   *  Stimuli generation  *
   ************************/

  logic sim_running;

  // data type
  typedef logic [DATA_BITS-1:0] data_t;

  class stimuli_t;
    // Constants
    static const bit [NUM_IN-1:0] all_ones = {NUM_IN{1'b1}};

    // signals
    rand bit                  error_before;
    rand bit                  error_after;

    rand bit                  gen_item;
    rand bit     [NUM_IN-1:0] valid_flip;
    rand bit     [NUM_IN-1:0] data_error;
    rand data_t  [NUM_IN-1:0] data_bitflips;

    rand bit                  raise_ready;

    // constraints disabled during tests
    constraint no_error      { error_before == 1'b0 && error_after == 1'b0 && valid_flip == '0;}
    constraint no_data_error { data_error  == '0;}
    constraint synchronous   { valid_flip inside {'0, all_ones};}
    constraint always_ready  { raise_ready == 1'b1;}
    constraint always_valid  { valid_flip == '0; gen_item == 1'b1; }

    // dependancy constraints
    constraint correct_flip{ foreach(data_bitflips[i]) if(!data_error[i]) data_bitflips[i] == '0;
                             foreach(data_bitflips[i]) if( data_error[i]) data_bitflips[i] != '0;}
    constraint not_all_flip{ error_before == '0 -> data_error != all_ones;
                             error_before == '0 -> valid_flip != all_ones;}

    // distribution constraints
    constraint d_error_dist{ data_error dist { '0 :/ 4, [('b1):all_ones] :/ 1}; }
    constraint valid_dist  { valid_flip dist { '0                   :/ 3,
                                               [('b1):(all_ones-1)] :/ 1,
                                               all_ones             :/ 1};
    }
    constraint error_dist  {
      error_before dist { 1'b0 := 3, 1'b1 := 1};
      error_after  dist { 1'b0 := 3, 1'b1 := 1};
    }
    constraint gen_item_dist {gen_item dist { 1'b0 := 3, 1'b1 := 1};}
  endclass

  // stimuli queue
  stimuli_t stimuli_queue [$];

  stimuli_t all_valid_stimuli;

  function automatic void generate_stimuli();
    // create default stimuli and results
    // default stimuli to retrieve buffered items
    all_valid_stimuli = new;
    all_valid_stimuli.error_before  = '0;
    all_valid_stimuli.error_after   = '0;
    all_valid_stimuli.gen_item      = 1'b1;
    all_valid_stimuli.valid_flip    = '0;
    all_valid_stimuli.data_error    = '0;
    all_valid_stimuli.data_bitflips = '0;
    all_valid_stimuli.raise_ready   = 1'b1;

    // 1st phase: check maximum throughput with no errors & no repeats
    for (int i = 0; i < 10; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");
      stimuli_queue.push_back(stimuli);
    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_valid_stimuli);
    end

    // 2nd phase: do random testing, no errors, no repeats
    for (int i = 0; i < 50; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // disable unused constraints
      stimuli.always_ready.constraint_mode(0);
      stimuli.always_valid.constraint_mode(0);
      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");
      stimuli_queue.push_back(stimuli);

    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_valid_stimuli);
    end

    // 3rd phase: do completely random testing
    for (int i = 0; i < 1000; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // disable unused constraints
      stimuli.always_ready.constraint_mode(0);
      stimuli.always_valid.constraint_mode(0);
      stimuli.synchronous.constraint_mode(0);
      stimuli.no_error.constraint_mode(0);
      stimuli.no_data_error.constraint_mode(0);
      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");
      stimuli_queue.push_back(stimuli);
    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_valid_stimuli);
    end
  endfunction : generate_stimuli

  /*******************
   *  apply stimuli  *
   *******************/

  // control signals
  logic error_before, error_after, join_error;
  logic gen_item;
  logic no_error;

  // Data input side
  data_t [NUM_IN-1:0] data_in, data_in_flipped, data_flip;
  logic  [NUM_IN-1:0] valid_in, valid_in_flipped, valid_flip;
  logic  [NUM_IN-1:0] ready_out;

  // Data output side
  data_t data_out;
  logic  raise_ready, ready_in, valid_out;

  // Testbench check signals
  data_t sink_expected, sink_received;
  logic  injected_error;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;
    // get the next stimuli
    wait (stimuli_queue.size() != '0);
    stimuli = stimuli_queue.pop_front();
    // Wait for apply time
    @(posedge clk);
    #(TApply);
    // apply stimuli
    error_before = stimuli.error_before;
    error_after = stimuli.error_after;
    gen_item = stimuli.gen_item;
    valid_flip = stimuli.valid_flip;
    data_flip = stimuli.data_bitflips;
    raise_ready = stimuli.raise_ready;
  endtask : apply_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  // source
  for(genvar i = 0; i < NUM_IN; i++) begin : gen_sources
    handshake_source #(
      .DATA_BITS ( DATA_BITS )
    ) i_source (
      .clk_i             ( clk          ),
      .rst_ni            ( rst_n        ),
      .next_item_i       ( gen_item     ),
      .allow_handshake_i ( no_error     ),
      .valid_o           ( valid_in[i]  ),
      .ready_i           ( ready_out[i] ),
      .data_o            ( data_in[i]   )
    );
  end

  assign no_error = !error_before & !error_after & !join_error;
  assign valid_in_flipped = valid_in ^ valid_flip;
  assign data_in_flipped = data_in ^ data_flip;

  dmr_handshake_join #(
    .T       ( data_t  ),
    .NUM_IN  ( NUM_IN  )
  ) i_dut (
    .clk_i          ( clk              ),
    .rst_ni         ( rst_n            ),
    .enable_i       ( 1'b1             ),
    .error_before_i ( error_before     ),
    .error_after_i  ( error_after      ),
    .error_o        ( join_error       ),
    .valid_i        ( valid_in_flipped ),
    .ready_o        ( ready_out        ),
    .data_i         ( data_in_flipped  ),
    .valid_o        ( valid_out        ),
    .ready_i        ( ready_in         ),
    .data_o         ( data_out         )
  );

  handshake_sink #(
    .DATA_BITS ( DATA_BITS )
    ) i_sink (
    .clk_i           ( clk           ),
    .rst_ni          ( rst_n         ),
    .raise_ready_i   ( raise_ready   ),
    .allow_sink_i    ( 1'b1          ),
    .valid_i         ( valid_out     ),
    .ready_o         ( ready_in      ),
    .data_i          ( data_out      ),
    .next_expected_o ( sink_expected ),
    .num_received_o  ( sink_received )
  );

  assign injected_error = error_before | |valid_flip | (&valid_in & |data_flip);

  /***********************
   *  Output collection  *
   ***********************/

  typedef struct packed {
    bit injected_error;
    bit detected_error;
  } result_t;

  result_t result_queue [$];

  task automatic collect_result;
    result_t result;
    // wait for test time
    @(posedge clk)
    #(TTest);
    // collect the results
    result.injected_error = injected_error;
    result.detected_error = join_error;
    result_queue.push_back(result);
    // check if we're done
    if(stimuli_queue.size() == 0) begin
      sim_running = 1'b0;
    end
  endtask : collect_result

  /*************
   *  Checker  *
   *************/

  time last_consumed = '0;

  task automatic check_result;
    automatic result_t result;

    do begin
      wait(result_queue.size() != 0);

      // extract the result
      result = result_queue.pop_front();

      // compare the results
      if(result.injected_error != result.detected_error)
        $error("[Data Error] Error injected in data not detected.");
    end while (sim_running);

    if(data_in[0] != sink_received) begin
      $error("[Data Error] Sent %d items, received %d items.", data_in[0], sink_received);
    end else begin
      $display("[Testbench] Received the correct number of items.");
    end
  endtask : check_result

  // Error assertions
  assert property (@(posedge clk) disable iff (~rst_n) ((error_before | error_after) & &ready_out |=> &ready_out)) else begin
    $error("[Ready Repetition] Ready was not repeated during a repeat cycle.");
  end

  // make sure output signals are consitent over all sources
  for (genvar i = 0; i < NUM_IN; i++) begin
    assert property(@(posedge clk) disable iff (~rst_n) (ready_out[i] == ready_out[0])) else begin
      $error("[Output Ready Mismatch] [OUT%d] reads %b, [OUT0] reads %b", i, ready_out[i], ready_out[0]);
    end
  end

  task run_apply();
    forever begin
      apply_stimuli();
    end
  endtask : run_apply

  task run_collect();
    forever begin
      collect_result();
    end
  endtask : run_collect

  initial begin : tb
    // Initialize variables
    error_after = '0;
    error_before = '0;
    gen_item = '0;
    sim_running = 1'b1;

    @(posedge rst_n)
    repeat(10) @(posedge clk);

    fork
      run_apply();
      run_collect();
      fork
        generate_stimuli();
        check_result();
      join
    join_any

    $display("[Testbench] Done.");
    $finish(0);
  end : tb

endmodule
