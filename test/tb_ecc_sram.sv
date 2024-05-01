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
// Description: Testbench for ecc_sram_wrap
// based on tb_tc_sram.sv in tech_cells_generic

module tb_ecc_sram;

  localparam BankSize       = 256;
  localparam AddrWidth      = $clog2(BankSize);
  localparam DataWidth      = 32;
  localparam ProtectedWidth = 39;
  localparam BEWidth        = DataWidth/8;

  localparam CyclTime = 10ns;
  localparam ApplTime = 2ns;
  localparam TestTime = 8ns;

  localparam int unsigned NoReq    = 200000; // Number of requests

  /********************************
   *  Helper tasks and variables  *
   ********************************/

  logic clk;
  logic rst_n;

  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  longint test_cnt;
  longint error_cnt;

  logic test_halfway;
  assign test_halfway = test_cnt > NoReq/2;

  task random_cycle_delay();
    repeat ($urandom_range(0,5)) @(posedge clk);
  endtask : random_cycle_delay

  task cycle_start();
    #ApplTime;
  endtask : cycle_start

  task cycle_end();
    #TestTime;
  endtask : cycle_end

  /************************
   *  Stimuli generation  *
   ************************/

  // Data types
  typedef logic [     AddrWidth-1:0] addr_t;
  typedef logic [     DataWidth-1:0] data_t;
  typedef logic [ProtectedWidth-1:0] prot_t;
  typedef logic [       BEWidth-1:0] be_t;

  class stimuli_t;
    rand data_t wdata;
    rand addr_t addr;
    rand be_t   be;
    rand logic  wen;

    constraint limit_addr {addr < BankSize;}
  endclass : stimuli_t

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden Values
  data_t golden_queue[$];

  // golden model
  data_t memory [BankSize-1:0];

  function automatic void generate_stimuli();
    repeat (1)
      for (int gen_i = 0; gen_i < NoReq; gen_i++) begin
        automatic stimuli_t stimuli = new;

        // Randomize
        if (stimuli.randomize()) begin
          stimuli_queue.push_back(stimuli);
          if (stimuli.wen) begin
            golden_queue.push_back(memory[stimuli.addr]);
          end else begin
            golden_queue.push_back({DataWidth{1'b?}});
            for (int unsigned j = 0; j < DataWidth; j++) begin
              if (stimuli.be[j/8]) begin
                memory[stimuli.addr][j] = stimuli.wdata[j];
              end
            end
          end
        end else begin
          $error("Could not randomize.");
        end
      end
  endfunction : generate_stimuli

  logic                 req, wen, gnt;
  logic [AddrWidth-1:0] addr;
  logic [DataWidth-1:0] wdata, rdata;
  logic [  BEWidth-1:0] be;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);
    cycle_start();

    stimuli = stimuli_queue.pop_front();
    req     = 1'b1;
    wen     = stimuli.wen;
    addr    = stimuli.addr;
    wdata   = stimuli.wdata;
    be      = stimuli.be;

    cycle_end();
    while (!gnt) begin
      @(posedge clk);
      cycle_start();
      cycle_end();
    end
    @(posedge clk);
    req = 1'b0;

  endtask : apply_stimuli

   /***********************
    *  Device Under Test  *
    ***********************/

  ecc_sram #(
    .NumWords         ( BankSize       ),
    .UnprotectedWidth ( DataWidth      ),
    .ProtectedWidth   ( ProtectedWidth ),
    .InputECC         ( 0              ),
    .NumRMWCuts       ( 1              ),
    .SimInit          ( "zeros"        )
  ) i_dut (
    .clk_i        ( clk ),
    .rst_ni       ( rst_n ),

    .scrub_trigger_i      ('0),
    .scrubber_fix_o       (),
    .scrub_uncorrectable_o(),

    .wdata_i ( wdata ),
    .addr_i  ( addr  ),
    .req_i   ( req   ),
    .we_i    ( ~wen  ),
    .be_i    ( be    ),
    .rdata_o ( rdata ),
    .gnt_o   ( gnt   ),

    .single_error_o       (),
    .multi_error_o        ()
  );

  /***********************
   *  Output collection  *
   ***********************/

  data_t result_queue [$];

  task collect_result();
    if (req && gnt) begin
      @(posedge clk)
      cycle_start();
      cycle_end();
      result_queue.push_back(rdata);
    end else begin
      @(posedge clk)
      cycle_start();
      cycle_end();
    end
  endtask : collect_result

  task automatic check_result;
    automatic data_t result;
    automatic data_t golden;

    do begin
      wait(result_queue.size() != 0);

      // Capture the result
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // Account for this check
      test_cnt++;

      if (result != golden) begin
        $warning("ERROR! Test %0d: expected 0x%h, found 0x%h.", test_cnt, golden, result);
        error_cnt++;
      end
    end while (golden_queue.size() != 0);
  endtask : check_result

  /****************
   *  Test Bench  *
   ****************/

  task run_apply();
    // Apply stimuli and collect results cycle
    forever begin
      apply_stimuli();
      random_cycle_delay();
    end
  endtask : run_apply

  task run_collect();
    cycle_start();
    cycle_end();
    forever begin
      collect_result();
    end
  endtask : run_collect

  initial begin : tb
    // Initialize variables
    test_cnt  = '0;
    error_cnt = '0;

    for (int i = 0; i < BankSize; i++) begin
      for (int j = 0; j < DataWidth; j++) begin
        memory[i][j] = 1'b0;
      end
    end

    req = 1'b0;
    wdata = '0;
    wen = '0;
    addr = '0;
    be = '0;
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
    if (error_cnt) $fatal(1, "Found %0d mismatches.", error_cnt);
    $finish();
  end : tb

endmodule

