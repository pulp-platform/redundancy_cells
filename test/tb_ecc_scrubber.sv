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

module tb_ecc_scrubber #(
  parameter int unsigned DataWidth = 39
);
  localparam int unsigned BankSize = 256;
  localparam int unsigned UseExternalECC = 0;

  localparam int unsigned RunCycles = 100000;
  localparam int unsigned ProtectBits = $clog2(DataWidth)+2;

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

  endclass : stimuli_t

  stimuli_t stimuli_queue [$];

  // Golden values
  typedef struct packed {

  } result_t;
  result_t golden_queue[$];

  function automatic void generate_stimuli();

  endfunction : generate_stimuli

  // Apply Stimuli

  task automatic apply_stimuli();
    
  endtask : apply_stimuli

  initial begin : init_stimuli

  end : init_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  ecc_scrubber #(
    .BankSize      (BankSize),
    .UseExternalECC(UseExternalECC)
  ) i_dut (
    .clk_i            (clk),
    .rst_ni           (rst_n),
    .scrub_trigger_i  (),
    .bit_corrections_o(),
    .intc_req_i       (),
    .intc_we_i        (),
    .intc_add_i       (),
    .intc_wdata_i     (),
    .intc_rdata_o     (),
    .bank_req_o       (),
    .bank_we_o        (),
    .bank_add_o       (),
    .bank_wdata_o     (),
    .bank_rdata_i     (),
    .ecc_out_o        (),
    .ecc_in_i         (),
    .ecc_err_i        ()
  );


endmodule
