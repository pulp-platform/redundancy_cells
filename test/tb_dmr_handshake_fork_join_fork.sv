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

// Test a series combination of a fork, join and fork handshake module
// to check if the combination fork-join and join-fork are compatible.

module tb_dmr_handshake_fork_join_fork;

  // Time Settings
  timeunit      1ns;
  timeprecision 1ps;

  // Number of outputs
  localparam int NUM_IN_OUT = 2;
  localparam int DATA_BITS  = 16;

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
    // constants
    static const bit [NUM_IN_OUT-1:0] all_ones = {NUM_IN_OUT{1'b1}};

    // non-random siganls
    static stimuli_t prev = null;
    bit any_error_injected;

    // signals
    rand bit    raise_valid;
    rand bit    flip_ready_0_F;
    rand bit    flip_ready_0_CB;
    rand bit    flip_valid_0_BC;
    rand data_t flip_data_0_BC;
    rand bit    pretend_error_before;
    rand bit    pretend_error_BC;
    rand bit    pretend_error_F;
    rand bit    pretend_error_CB;
    rand bit    pretend_error_after;

    // constraints disabled during tests
    constraint no_error      {
      !flip_ready_0_F &
      !flip_ready_0_CB &
      !flip_valid_0_BC &
      (flip_data_0_BC == '0) &
      !pretend_error_before &
      !pretend_error_BC &
      !pretend_error_F &
      !pretend_error_CB &
      !pretend_error_after;
    }
    constraint always_ready  {
      !flip_ready_0_F &
      !flip_ready_0_CB &
      !flip_valid_0_BC;
    }
    constraint always_valid  {
      raise_valid == 1'b1;
    }

    // only allow errors to propagate forwards
    // data flips are ignored as they do not always cause an error
    constraint forward_prop_only {
      if(prev != null && prev.any_error_injected) {
        !prev.pretend_error_before -> !pretend_error_before;
        !prev.pretend_error_before &
        !prev.pretend_error_BC -> !pretend_error_BC;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC -> !flip_valid_0_BC;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC &
        !prev.flip_data_0_BC -> !flip_data_0_BC;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC &
        !prev.pretend_error_F -> !pretend_error_F;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC &
        !prev.pretend_error_F &
        !prev.flip_ready_0_F -> !flip_ready_0_F;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC &
        !prev.pretend_error_F &
        !prev.flip_ready_0_F &
        !prev.pretend_error_CB -> !pretend_error_CB;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC &
        !prev.pretend_error_F &
        !prev.flip_ready_0_F &
        !prev.pretend_error_CB &
        !prev.flip_ready_0_CB -> !flip_ready_0_CB;
        !prev.pretend_error_before &
        !prev.pretend_error_BC &
        !prev.flip_valid_0_BC &
        !prev.pretend_error_F &
        !prev.flip_ready_0_F &
        !prev.pretend_error_CB &
        !prev.flip_ready_0_CB &
        !prev.pretend_error_after -> !pretend_error_after;
      }
    }

    // distribution constraints
    constraint error_dist {
      flip_ready_0_F       dist { 1'b0 := 4, 1'b1 := 1};
      flip_ready_0_CB      dist { 1'b0 := 4, 1'b1 := 1};
      flip_valid_0_BC      dist { 1'b0 := 4, 1'b1 := 1};
      pretend_error_before dist { 1'b0 := 4, 1'b1 := 1};
      pretend_error_BC     dist { 1'b0 := 4, 1'b1 := 1};
      pretend_error_F      dist { 1'b0 := 4, 1'b1 := 1};
      pretend_error_CB     dist { 1'b0 := 4, 1'b1 := 1};
      pretend_error_after  dist { 1'b0 := 4, 1'b1 := 1};
    }
    constraint d_error_dist {
      flip_data_0_BC dist { '0 :/ 4, [('b1):all_ones] :/ 1};
    }

    function void post_randomize ();
      any_error_injected =
        flip_ready_0_F |
        flip_ready_0_CB |
        flip_valid_0_BC |
        |flip_data_0_BC |
        pretend_error_before |
        pretend_error_BC |
        pretend_error_F |
        pretend_error_CB |
        pretend_error_after;

      // override stimuli
      prev = this;
    endfunction

  endclass

  // stimuli queue
  stimuli_t stimuli_queue [$];

  // result type
  typedef struct packed {
    bit error;
  } result_t;

  result_t golden_queue [$];

  stimuli_t all_ready_stimuli;
  result_t no_error_result;

  function automatic void generate_stimuli();
    // create default stimuli and results
    // default stimuli to retrieve buffered items
    all_ready_stimuli = new;
    if (!all_ready_stimuli.randomize()) $error("Could not randomize.");
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
      stimuli.always_ready.constraint_mode(0);
      stimuli.always_valid.constraint_mode(0);
      // Randomize
      if (!stimuli.randomize()) $error("Could not randomize.");

      stimuli_queue.push_back(stimuli);
      golden_queue.push_back('{error: stimuli.any_error_injected });
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

  // Single-side signals
  logic  valid_A, valid_D, valid_E;
  logic  ready_A, ready_D, ready_E;
  data_t data_A, data_D, data_E;

  // DMR-side signals
  logic  [NUM_IN_OUT-1:0] valid_B, valid_C, valid_F;
  logic  [NUM_IN_OUT-1:0] ready_B, ready_C, ready_F;
  data_t [NUM_IN_OUT-1:0] data_B, data_C, data_F;

  // Injection signals
  logic flip_valid_0_BC;
  data_t flip_data_0_BC;
  logic flip_ready_0_F;
  logic flip_ready_0_CB;

  // Pretended Error signals
  logic pretend_error_before;
  logic pretend_error_BC;
  logic pretend_error_F;
  logic pretend_error_CB;
  logic pretend_error_after;

  // Fork and join control signals
  logic error_before_AB, error_before_CD, error_before_EF;
  logic error_out_AB, error_out_CD, error_out_EF;
  logic error_after_AB, error_after_CD, error_after_EF;

  // Source and sink signals
  logic                  raise_valid;
  logic [NUM_IN_OUT-1:0] raise_ready;
  logic [NUM_IN_OUT-1:0] sink_ready;
  logic                  no_error;

  // Testbench check signals
  data_t [NUM_IN_OUT-1:0] sink_expected, sink_received;

  // initialize TB signals
  initial begin
    flip_ready_0_F = '0;
    flip_ready_0_CB = '0;
    raise_valid = '0;
    flip_valid_0_BC = '0;
    flip_data_0_BC = '0;
    pretend_error_before = '0;
    pretend_error_BC = '0;
    pretend_error_F = '0;
    pretend_error_CB = '0;
    pretend_error_after = '0;
  end

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    // Get the next stimuli
    wait (stimuli_queue.size() != '0);
    stimuli = stimuli_queue.pop_front();

    // Wait for apply time
    @(posedge clk);
    #(TApply);

    // apply stimuli
    flip_ready_0_F = stimuli.flip_ready_0_F;
    flip_ready_0_CB = stimuli.flip_ready_0_CB;
    raise_valid = stimuli.raise_valid;
    flip_valid_0_BC = stimuli.flip_valid_0_BC;
    flip_data_0_BC = stimuli.flip_data_0_BC;
    pretend_error_before = stimuli.pretend_error_before;
    pretend_error_BC = stimuli.pretend_error_BC;
    pretend_error_F = stimuli.pretend_error_F;
    pretend_error_CB = stimuli.pretend_error_CB;
    pretend_error_after = stimuli.pretend_error_after;

  endtask : apply_stimuli

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
    .valid_o           ( valid_A     ),
    .ready_i           ( ready_A     ),
    .data_o            ( data_A      )
  );

  // Fork AB
  dmr_handshake_fork #(
    .T       ( data_t     ),
    .NUM_OUT ( NUM_IN_OUT )
  ) i_dut_fork_AB (
    .clk_i          ( clk             ),
    .rst_ni         ( rst_n           ),
    .enable_i       ( 1'b1            ),
    .error_before_i ( error_before_AB ),
    .error_after_i  ( error_after_AB  ),
    .error_o        ( error_out_AB    ),
    .valid_i        ( valid_A         ),
    .ready_o        ( ready_A         ),
    .data_i         ( data_A          ),
    .valid_o        ( valid_B         ),
    .ready_i        ( ready_B         ),
    .data_o         ( data_B          )
  );

  // Fault injection BC
  assign valid_C[0] = valid_B[0] ^ flip_valid_0_BC;
  assign data_C[0] = data_B[0] ^ flip_data_0_BC;
  assign ready_B[0] = ready_C[0] ^ flip_ready_0_CB;
  // Assign unflipped signals
  assign valid_C[NUM_IN_OUT-1:1] = valid_B[NUM_IN_OUT-1:1];
  assign data_C[NUM_IN_OUT-1:1] = data_B[NUM_IN_OUT-1:1];
  assign ready_B[NUM_IN_OUT-1:1] = ready_C[NUM_IN_OUT-1:1];

  // Join CD
  dmr_handshake_join #(
    .T       ( data_t     ),
    .NUM_IN  ( NUM_IN_OUT )
  ) i_dut_join_CD (
    .clk_i          ( clk             ),
    .rst_ni         ( rst_n           ),
    .enable_i       ( 1'b1            ),
    .error_before_i ( error_before_CD ),
    .error_after_i  ( error_after_CD  ),
    .error_o        ( error_out_CD    ),
    .valid_i        ( valid_C         ),
    .ready_o        ( ready_C         ),
    .data_i         ( data_C          ),
    .valid_o        ( valid_D         ),
    .ready_i        ( ready_D         ),
    .data_o         ( data_D          )
  );

  // assign unflipped signals DE
  assign valid_E = valid_D;
  assign data_E = data_D;
  assign ready_D = ready_E;

  // Fork EF
  dmr_handshake_fork #(
    .T       ( data_t     ),
    .NUM_OUT ( NUM_IN_OUT )
  ) i_dut_fork_EF (
    .clk_i          ( clk             ),
    .rst_ni         ( rst_n           ),
    .enable_i       ( 1'b1            ),
    .error_before_i ( error_before_EF ),
    .error_after_i  ( error_after_EF  ),
    .error_o        ( error_out_EF    ),
    .valid_i        ( valid_E         ),
    .ready_o        ( ready_E         ),
    .data_i         ( data_E          ),
    .valid_o        ( valid_F         ),
    .ready_i        ( ready_F         ),
    .data_o         ( data_F          )
  );

  // make ready signal depend on valid
  assign raise_ready = valid_F;

  assign ready_F[0] = sink_ready[0] ^ flip_ready_0_F;
  assign ready_F[NUM_IN_OUT-1:1] = sink_ready[NUM_IN_OUT-1:1];

  // Sinks
  for(genvar i = 0; i < NUM_IN_OUT; i++) begin : gen_sink
     handshake_sink #(
      .DATA_BITS ( DATA_BITS )
     ) i_sink (
      .clk_i           ( clk              ),
      .rst_ni          ( rst_n            ),
      .raise_ready_i   ( raise_ready[i]   ),
      .allow_sink_i    ( no_error         ),
      .valid_i         ( valid_F[i]       ),
      .ready_o         ( sink_ready[i]    ),
      .data_i          ( data_F[i]        ),
      .next_expected_o ( sink_expected[i] ),
      .num_received_o  ( sink_received[i] )
    );
  end

  // Error interconnect
  assign no_error = ~(error_before_AB | error_before_CD | error_before_EF | error_out_AB | error_out_CD | error_out_EF | error_after_AB | error_after_CD | error_after_EF);
  assign error_before_AB = pretend_error_before | pretend_error_BC | pretend_error_F | pretend_error_CB | error_out_CD | error_out_EF;
  assign error_before_CD = pretend_error_before | pretend_error_BC;
  assign error_before_EF = pretend_error_before | pretend_error_BC | pretend_error_F | error_out_CD;
  assign error_after_AB = pretend_error_after;
  assign error_after_CD = pretend_error_F | pretend_error_CB | error_out_EF | error_out_AB | pretend_error_after;
  assign error_after_EF = pretend_error_CB | error_out_AB | pretend_error_after;

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  task automatic collect_result;
    result_t result;
    // wait for test time
    @(posedge clk)
    #(TTest);
    // collect the results (with manual flip data correction)
    result.error = ~no_error | |flip_data_0_BC;
    result_queue.push_back(result);
  endtask : collect_result

  /*************
   *  Checker  *
   *************/

  task automatic check_result;
    automatic result_t result, golden;

    do begin
      wait(result_queue.size() != 0);

      // extract the result
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // compare the results
      if(golden != result)
        $error("[Error] Injected Error not detected.");
    end while (golden_queue.size() != 0);

    // Check if correct number of items received
    for(int unsigned i = 0; i < NUM_IN_OUT; i++) begin
      if(data_A != sink_received[i]) begin
        $error("[Data Error] Sent %d items, sink %d, received %d items.", data_A, i, sink_received[i]);
      end
    end
  endtask : check_result

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

    $display("[Testbench] Done. Transmitted %0d Data Items.", data_A);
    $finish(0);
  end : tb

endmodule
