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

module tb_dmr_handshake_fork;

  // Time Settings
  timeunit      1ns;
  timeprecision 1ps;

  // Number of outputs
  localparam int NUM_OUT   = 2;
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

  // data type
  typedef logic [DATA_BITS-1:0] data_t;

  class stimuli_t;
    // Constants
    static const bit [NUM_OUT-1:0] all_ones = {NUM_OUT{1'b1}};

    // signals
    rand bit                   error_before;
    rand bit                   error_after;

    rand bit     [NUM_OUT-1:0] ready_flip;
    rand bit                   raise_valid;

    // fixed constraints
    constraint save_flip     { ready_flip == all_ones -> error_before == 1'b1;}

    // constraints disabled during tests
    constraint no_error      { error_before == 1'b0 && error_after == 1'b0 && ready_flip == '0;}
    constraint synchronous   { ready_flip inside {'0, all_ones};}
    constraint always_ready  { ready_flip == '0;}
    constraint always_valid  { raise_valid == 1'b1;}

    // distribution constraints
    constraint ready_dist  { ready_flip dist { '0                   :/ 1,
                                               [('b1):(all_ones-1)] :/ 1,
                                               all_ones             :/ 1};}
    constraint error_dist  {
      error_before dist { 1'b0 := 3, 1'b1 := 1};
      error_after  dist { 1'b0 := 3, 1'b1 := 1};
    }

  endclass

  // stimuli queue
  stimuli_t stimuli_queue [$];

  // result type
  typedef struct packed {
    bit error;
  } expected_result_t;

  expected_result_t golden_queue [$];

  stimuli_t all_ready_stimuli;
  expected_result_t no_error_result;

  function automatic void generate_stimuli();
    // create default stimuli and results
    // default stimuli to retrieve buffered items
    all_ready_stimuli = new;
    all_ready_stimuli.error_before  = '0;
    all_ready_stimuli.error_after   = '0;
    all_ready_stimuli.raise_valid   = '0;
    all_ready_stimuli.ready_flip    = '0;
    // default result to retrieve buffered items
    no_error_result = '{ error: '0 };

    // 1st phase: check maximum throughput with no errors & no repeats
    for (int i = 0; i < 10; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");

      stimuli_queue.push_back(stimuli);
      golden_queue.push_back('{error: '0});

    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_ready_stimuli);
      golden_queue.push_back(no_error_result);
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
      golden_queue.push_back('{error: '0});

    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_ready_stimuli);
      golden_queue.push_back(no_error_result);
    end

    // 3rd phase: do completely random testing
    for (int i = 0; i < 1000; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // disable unused constraints
      stimuli.no_error.constraint_mode(0);
      stimuli.synchronous.constraint_mode(0);
      stimuli.always_ready.constraint_mode(0);
      stimuli.always_valid.constraint_mode(0);
      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");

      stimuli_queue.push_back(stimuli);
      golden_queue.push_back('{error: !(~|ready_in | &ready_in)});

    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_ready_stimuli);
      golden_queue.push_back(no_error_result);
    end
  endfunction : generate_stimuli

  /*******************
   *  apply stimuli  *
   *******************/

  // control signals
  logic error_before, error_after, fork_error;
  logic raise_valid;
  logic no_error;

  // Data input side
  data_t data_in;
  logic  valid_in, ready_out;

  // Data output side
  data_t [NUM_OUT-1:0] data_out;
  logic  [NUM_OUT-1:0] ready_in, valid_out, ready_in_flip;

  // Testbench check signals
  data_t [NUM_OUT-1:0] sink_expected, sink_received;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;
    // get the next stimuli
    wait (stimuli_queue.size() != '0);
    stimuli = stimuli_queue.pop_front();
    // Wait for apply time
    @(posedge clk);
    #(TApply);
    // apply stimuli
    // only update ready in signals if the prev cycle had no error_after
    if(error_after) begin
      ready_in_flip = ready_in;
    end else begin
      ready_in_flip = ready_in ^ stimuli.ready_flip;
    end
    error_before = stimuli.error_before;
    raise_valid = stimuli.raise_valid;
    error_after = stimuli.error_after;
  endtask : apply_stimuli

  assign no_error = !error_before & !error_after & !fork_error;

  /***********************
   *  Device Under Test  *
   ***********************/

  // source
  handshake_source #(
    .DATA_BITS ( DATA_BITS )
  ) i_source (
    .clk_i             ( clk         ),
    .rst_ni            ( rst_n       ),
    .next_item_i       ( raise_valid ),
    .allow_handshake_i ( 1'b1        ),
    .valid_o           ( valid_in    ),
    .ready_i           ( ready_out   ),
    .data_o            ( data_in     )
  );

  // dut
  dmr_handshake_fork #(
    .T       ( data_t  ),
    .NUM_OUT ( NUM_OUT )
  ) i_dut (
    .clk_i          ( clk           ),
    .rst_ni         ( rst_n         ),
    .error_before_i ( error_before  ),
    .error_after_i  ( error_after   ),
    .error_o        ( fork_error    ),
    .valid_i        ( valid_in      ),
    .ready_o        ( ready_out     ),
    .data_i         ( data_in       ),
    .valid_o        ( valid_out     ),
    .ready_i        ( ready_in_flip ),
    .data_o         ( data_out      )
  );

  // sinks
  for(genvar i = 0; i < NUM_OUT; i++) begin : gen_sink
     handshake_sink #(
      .DATA_BITS ( DATA_BITS )
     ) i_sink (
      .clk_i           ( clk              ),
      .rst_ni          ( rst_n            ),
      .raise_ready_i   ( 1'b1             ),
      .allow_sink_i    ( no_error         ),
      .valid_i         ( valid_out[i]     ),
      .ready_o         ( ready_in[i]      ),
      .data_i          ( data_out[i]      ),
      .next_expected_o ( sink_expected[i] ),
      .num_received_o  ( sink_received[i] )
    );
  end

  /***********************
   *  Output collection  *
   ***********************/

  typedef struct packed {
    bit error;
    bit ready_out;
    bit valid_out;
    bit    [NUM_OUT-1:0] received_data;
    data_t [NUM_OUT-1:0] data;
  } result_t;

  result_t result_queue [$];

  task automatic collect_result;
    result_t result;
    // wait for test time
    @(posedge clk)
    #(TTest);
    // collect the results
    result.error = fork_error;
    result.ready_out = ready_out;
    result.valid_out = &valid_out;
    result.received_data = valid_out & ready_in & {NUM_OUT{~(fork_error | error_before | error_after)}};
    result.data = data_out;
    result_queue.push_back(result);
  endtask : collect_result

  /*************
   *  Checker  *
   *************/

  task automatic check_result;
    automatic result_t result;
    automatic expected_result_t golden;

    do begin
      wait(result_queue.size() != 0);

      // extract the result
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // compare the results
      if(golden.error & !result.error)
        $error("[Error] Error injected in outgoing handshake not detected.");
    end while (golden_queue.size() != 0);

    for(int unsigned i = 0; i < NUM_OUT; i++) begin
      if(data_in != sink_received[i]) begin
        $error("[Data Error] Sent %d items, sink %d, received %d items.", data_in, i, sink_received[i]);
      end
    end
  endtask : check_result

  // Error assertions
  assert property (@(posedge clk) disable iff (~rst_n) ((error_before | error_after) & &valid_out |=> $stable(data_out))) else begin
    $error("[Data Repetition] Data was not repeated after error.");
  end

  // make sure output signals are consitent over all outputs
  for (genvar i = 0; i < NUM_OUT; i++) begin
    assert property(@(posedge clk) disable iff (~rst_n) (data_out[i] == data_out[0])) else begin
      $error("[Output Data Mismatch] [OUT%d] reads %d, [OUT0] reads %d", i, data_out[i], data_out[0]);
    end
    assert property(@(posedge clk) disable iff (~rst_n) (valid_out[i] == valid_out[0])) else begin
      $error("[Output Valid Mismatch] [OUT%d] reads %b, [OUT0] reads %b", i, valid_out[i], valid_out[0]);
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
    raise_valid = '0;

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

    $display("[Testbench] Transmitted %0d Data Items.", data_in);
    $display("[Testbench] Done.");
    $finish(0);
  end : tb

endmodule
