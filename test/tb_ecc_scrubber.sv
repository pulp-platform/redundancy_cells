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
// Description: Testbench for ecc_scrubber
// 
// 
// TODO: INTC interference currently untested

module tb_ecc_scrubber #(
  parameter int unsigned DataWidth = 39
);
  localparam int unsigned BankSize = 256;
  localparam int unsigned UseExternalECC = 0;

  localparam int unsigned RunCycles = 100000;
  localparam int unsigned ProtectBits = $clog2(DataWidth)+2;

  localparam int unsigned NoReq = 20000; // Number of requests

  /******************
   *  Helper tasks  *
   ******************/

  localparam time         CyclTime  = 10ns;
  localparam time         TTest     = 8ns;
  localparam time         TApply    = 2ns;


  logic clk;
  logic rst_n;

  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

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
  typedef logic [DataWidth-1:0] data_t;

  class stimuli_t;
    rand logic [31:0] unprot_data;
    rand bit error;
    rand int unsigned error_pos;
    data_t data;
    data_t inject;

    function data_t get_inject;
      inject = '0;
      inject[error_pos] = 1'b1;
      return inject;
    endfunction : get_inject

    function data_t get_data;
      data = prim_secded_pkg::prim_secded_39_32_enc(unprot_data);
      return data;
    endfunction : get_data

    constraint error_limit {error_pos < DataWidth;}
  endclass : stimuli_t

  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {
    bit                          error;
    data_t                       corrected;
    logic                        bit_corrections;
    logic [$clog2(BankSize)-1:0] add;
  } result_t;
  result_t golden_queue[$];


  function automatic void generate_stimuli();
    logic corr;
    corr = '0;

    repeat (1)
      for (int gen_i = 0; gen_i < NoReq; gen_i++) begin
        automatic stimuli_t stimuli = new;

        stimuli.error_limit.constraint_mode(1);

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          golden_queue.push_back('{error: stimuli.error, corrected: stimuli.get_data(), bit_corrections: stimuli.error, add: gen_i % BankSize});
        end else begin
          $error("Could not randomize.");
        end
      end
  endfunction : generate_stimuli

  // Apply Stimuli

  logic                        scrub_trigger;
  logic                        bit_corrections;
  logic                        intc_req;
  logic                        intc_we;
  logic [$clog2(BankSize)-1:0] intc_add;
  logic [       DataWidth-1:0] intc_wdata;
  logic [       DataWidth-1:0] intc_rdata;

  logic [       DataWidth-1:0] bank_rdata;
  logic                        bank_req;
  logic                        bank_we;
  logic [$clog2(BankSize)-1:0] bank_add;
  logic [       DataWidth-1:0] bank_wdata;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);
    cycle_start();

    stimuli = stimuli_queue.pop_front();

    scrub_trigger = 1'b1;

    @(posedge clk)
    cycle_start();
    scrub_trigger = 1'b0;
    cycle_end();
    if (bank_req && !bank_we) begin
      @(posedge clk)
      cycle_start();
      if (stimuli.error) begin
        bank_rdata    = stimuli.get_data() ^ stimuli.get_inject();
      end else begin
        bank_rdata    = stimuli.get_data();
      end
      @(posedge clk)
      cycle_start();
      bank_rdata = '0;
    end else begin
      $error("ERROR! Not requesting data for scrub.");
    end
  endtask : apply_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  ecc_scrubber #(
    .BankSize      (BankSize),
    .UseExternalECC(UseExternalECC)
  ) i_dut (
    .clk_i            ( clk             ),
    .rst_ni           ( rst_n           ),
    .scrub_trigger_i  ( scrub_trigger   ),
    .bit_corrected_o  ( bit_corrections ),
    .uncorrectable_o  (),
    .intc_req_i       ( intc_req        ),
    .intc_we_i        ( intc_we         ),
    .intc_add_i       ( intc_add        ),
    .intc_wdata_i     ( intc_wdata      ),
    .intc_rdata_o     ( intc_rdata      ),
    .bank_req_o       ( bank_req        ),
    .bank_we_o        ( bank_we         ),
    .bank_add_o       ( bank_add        ),
    .bank_wdata_o     ( bank_wdata      ),
    .bank_rdata_i     ( bank_rdata      ),
    .ecc_out_o        (                 ),
    .ecc_in_i         ( '0              ),
    .ecc_err_i        ( '0              )
  );

  /***********************
   *  Output collection  *
   ***********************/

  result_t result_queue [$];

  logic [$clog2(BankSize)-1:0] tmp_add;

  task automatic collect_result;
    cycle_start();
    cycle_end();
    if (scrub_trigger) begin
      // result_queue.push_back('{error: 0, corrected: {DataWidth{1'b?}}, bit_corrections: '0, add: bank_add});
      // $display("Bank Address: 0x%h",bank_add);
      @(posedge clk)
      cycle_start();
      cycle_end();
      tmp_add = bank_add;
      @(posedge clk)
      cycle_start();
      cycle_end();
      if (bank_req && bank_we) begin
        result_queue.push_back('{error: 1, corrected: bank_wdata, bit_corrections: bit_corrections, add: tmp_add});
      end else begin
        result_queue.push_back('{error: 0, corrected: {DataWidth{1'b?}}, bit_corrections: bit_corrections, add: tmp_add});
      end
    end
  endtask : collect_result

  task automatic check_result;
    automatic result_t result;
    automatic result_t golden;

    do begin
      wait(result_queue.size() != 0);

      // Capture the result
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // Account for this check
      test_cnt++;

      if (result != golden) begin
        $warning("ERROR! Test %0d: expected 0x%h, found 0x%h.", test_cnt, golden, result);
        $display("golden: error: %0d, corrected: 0x%h, bit_corrections: %0d, add: 0x%h", golden.error, golden.corrected, golden.bit_corrections, golden.add);
        $display("result: error: %0d, corrected: 0x%h, bit_corrections: %0d, add: 0x%h", result.error, result.corrected, result.bit_corrections, result.add);

        error_cnt++;
      end
    end while (golden_queue.size() != 0);
  endtask : check_result

  /****************
   *  Test Bench  *
   ****************/

  task run_apply();
    forever begin
      apply_stimuli();
      repeat(10) @(posedge clk);
    end
  endtask : run_apply

  task run_collect();
    forever begin
      collect_result();
    end
  endtask : run_collect

  initial begin : tb
    // Initialize variables
    test_cnt  = '0;
    error_cnt = '0;

    scrub_trigger = '0;
    intc_req = '0;
    intc_we = '0;
    intc_add = '0;
    intc_wdata = '0;
    bank_rdata = '0;
    
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

    $display("Checked %0d tests, found %0d mismatches.", test_cnt, error_cnt);
    $finish(error_cnt);
  end : tb

endmodule
