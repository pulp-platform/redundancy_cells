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
// Description: Testbench for ecc_sram
// based on tb_tc_sram.sv in tech_cells_generic
//
// A random phase checks the data against a golden model (test/ecc_sram_fault_injection.tcl flips
// one bit per word halfway through it). With HwInitEnabled, it also pulses init_i at random, which
// zeroes the golden model. A directed phase then injects bit flips into the SRAM read data, the
// read-modify-write cut and the write data, and checks the data and the cycle in which
// single_error_o / multi_error_o report them.

module tb_ecc_sram #(
  parameter bit          InputECC          = 1'b0,
  parameter int unsigned NumRMWCuts        = 1,
  parameter int unsigned BankAccessLatency = 1,
  parameter bit          HwInitEnabled     = 1'b0,
  parameter int unsigned NoReq             = 200000 // Number of random requests
);

  localparam BankSize       = 256;
  localparam AddrWidth      = $clog2(BankSize);
  localparam DataWidth      = 32;
  localparam ProtectedWidth = 39;
  localparam BEWidth        = DataWidth/8;
  localparam DutWidth       = InputECC ? ProtectedWidth : DataWidth;

  localparam CyclTime = 10ns;
  localparam ApplTime = 2ns;
  localparam TestTime = 8ns;

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
  assign test_halfway = test_cnt > longint'(NoReq)/2;

  // Cycle count, sampled at TestTime
  longint unsigned cycle;
  always @(posedge clk) cycle++;

  // All tasks below start and end at ApplTime of a cycle
  task automatic next_cycle();
    @(posedge clk);
    #ApplTime;
  endtask : next_cycle

  task automatic to_test_time();
    #(TestTime - ApplTime);
  endtask : to_test_time

  /************************
   *  Stimuli generation  *
   ************************/

  // Data types
  typedef logic [     AddrWidth-1:0] addr_t;
  typedef logic [     DataWidth-1:0] data_t;
  typedef logic [ProtectedWidth-1:0] prot_t;
  typedef logic [       BEWidth-1:0] be_t;

  class stimuli_t;
    rand data_t       wdata;
    rand addr_t       addr;
    rand be_t         be;
    rand logic        we;
    // Instead of a request, hold init_i high for hw_init_cycles
    rand logic        hw_init;
    rand int unsigned hw_init_cycles;

    constraint limit_addr {addr < BankSize;}
    constraint limit_hw_init {
      hw_init dist {1'b1 := HwInitEnabled, 1'b0 := 999};
      hw_init_cycles inside {[1:20]};
    }
  endclass : stimuli_t

  typedef struct {
    logic  check;
    data_t data;
  } golden_t;

  // Stimuli
  stimuli_t stimuli_queue [$];

  // Golden Values
  golden_t golden_queue[$];

  // golden model
  data_t memory [BankSize-1:0];

  function automatic data_t apply_write(data_t old, data_t wdata, be_t be);
    apply_write = old;
    for (int unsigned i = 0; i < BEWidth; i++) begin
      if (be[i]) apply_write[i*8 +: 8] = wdata[i*8 +: 8];
    end
  endfunction

  function automatic void generate_stimuli();
    for (int gen_i = 0; gen_i < NoReq; gen_i++) begin
      automatic stimuli_t stimuli = new;

      // Randomize
      if (stimuli.randomize()) begin
        stimuli_queue.push_back(stimuli);
        // Everything before an initialization is overwritten with zeros, it returns no data
        if (stimuli.hw_init) begin
          foreach (memory[i]) memory[i] = '0;
        end else if (!stimuli.we) begin
          golden_queue.push_back('{check: 1'b1, data: memory[stimuli.addr]});
        end else begin
          golden_queue.push_back('{check: 1'b0, data: 'x});
          memory[stimuli.addr] = apply_write(memory[stimuli.addr], stimuli.wdata, stimuli.be);
        end
      end else begin
        $error("Could not randomize.");
      end
    end
  endfunction : generate_stimuli

  logic                 req, we, gnt, hw_init;
  logic [AddrWidth-1:0] addr;
  logic [DataWidth-1:0] wdata, rdata;
  logic [  BEWidth-1:0] be;
  // Bits flipped in the write codeword, InputECC only
  prot_t                wdata_flip;
  // ECC errors found by the testbench in the read codeword, InputECC only
  logic [1:0]           rdata_error;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;

    wait (stimuli_queue.size() != '0);

    stimuli = stimuli_queue.pop_front();
    if (stimuli.hw_init) begin
      hw_init = 1'b1;
      repeat (stimuli.hw_init_cycles) next_cycle();
      hw_init = 1'b0;
      return;
    end
    req     = 1'b1;
    we      = stimuli.we;
    addr    = stimuli.addr;
    wdata   = stimuli.wdata;
    be      = stimuli.be;

    to_test_time();
    while (!gnt) begin
      @(posedge clk);
      #TestTime;
    end
    next_cycle();
    req = 1'b0;

  endtask : apply_stimuli

   /***********************
    *  Device Under Test  *
    ***********************/

  logic [DutWidth-1:0] dut_wdata, dut_rdata;
  logic                single_error, multi_error;

  if (InputECC) begin : gen_input_ecc
    prot_t wdata_enc;

    hsiao_ecc_enc #(
      .DataWidth ( DataWidth                  ),
      .ProtWidth ( ProtectedWidth - DataWidth )
    ) i_enc (
      .in  ( wdata     ),
      .out ( wdata_enc )
    );

    hsiao_ecc_dec #(
      .DataWidth ( DataWidth                  ),
      .ProtWidth ( ProtectedWidth - DataWidth )
    ) i_dec (
      .in        ( dut_rdata   ),
      .out       ( rdata       ),
      .syndrome_o(),
      .err_o     ( rdata_error )
    );

    assign dut_wdata = wdata_enc ^ wdata_flip;
  end else begin : gen_no_input_ecc
    assign dut_wdata   = wdata;
    assign rdata       = dut_rdata;
    assign rdata_error = '0;
  end

  ecc_sram #(
    .NumWords          ( BankSize          ),
    .UnprotectedWidth  ( DataWidth         ),
    .ProtectedWidth    ( ProtectedWidth    ),
    .InputECC          ( InputECC          ),
    .NumRMWCuts        ( NumRMWCuts        ),
    .SimInit           ( HwInitEnabled ? "random" : "zeros" ),
    .HwInitEnabled     ( HwInitEnabled     ),
    .BankAccessLatency ( BankAccessLatency )
  ) i_dut (
    .clk_i        ( clk ),
    .rst_ni       ( rst_n ),

    .scrub_trigger_i      ('0),
    .scrubber_fix_o       (),
    .scrub_uncorrectable_o(),

    .init_i  ( hw_init   ),

    .wdata_i ( dut_wdata ),
    .addr_i  ( addr      ),
    .req_i   ( req       ),
    .we_i    ( we        ),
    .be_i    ( be        ),
    .accum_i ( '0        ),
    .rdata_o ( dut_rdata ),
    .gnt_o   ( gnt       ),

    .single_error_o ( single_error ),
    .multi_error_o  ( multi_error  )
  );

  /***********************
   *  Output collection  *
   ***********************/

  data_t result_queue [$];

  // Read data returns BankAccessLatency cycles after the grant
  task automatic run_collect();
    automatic bit granted [$];
    forever begin
      to_test_time();
      granted.push_back(req && gnt);
      if (granted.size() > BankAccessLatency) begin
        if (granted.pop_front()) result_queue.push_back(rdata);
      end
      next_cycle();
    end
  endtask : run_collect

  task automatic check_result;
    automatic data_t   result;
    automatic golden_t golden;

    do begin
      wait(result_queue.size() != 0);

      // Capture the result
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // Account for this check
      test_cnt++;

      if (golden.check && result != golden.data) begin
        $warning("ERROR! Test %0d: expected 0x%h, found 0x%h.", test_cnt, golden.data, result);
        error_cnt++;
      end
    end while (golden_queue.size() != 0);
  endtask : check_result

  /***********************
   *  Error flag monitor  *
   ***********************/

  typedef struct {
    longint unsigned cycle;
    logic            single;
    logic            multi;
  } flag_t;

  flag_t flag_queue [$];
  logic  random_phase;

  always @(posedge clk) begin
    #TestTime;
    if (single_error || multi_error) begin
      // Nothing is flipped before the fault injection script kicks in halfway
      if (random_phase && !test_halfway) begin
        $warning("ERROR! ECC error reported in cycle %0d before any fault was injected.", cycle);
        error_cnt++;
      end
      flag_queue.push_back('{cycle: cycle, single: single_error, multi: multi_error});
    end
  end

  /*********************
   *  Fault injection  *
   *********************/

  // Flip bits of the word the SRAM currently outputs (tc_sram simulation model)
  task automatic flip_sram_rdata(prot_t mask);
    $deposit(i_dut.i_bank.rdata_q[0][0], i_dut.i_bank.rdata_q[0][0] ^ mask);
  endtask : flip_sram_rdata

  // Flip bits of the codeword at the end of the read-modify-write cut
  event  flip_cut;
  prot_t flip_cut_mask;
  if (NumRMWCuts > 0) begin : gen_cut_flip
    always @(flip_cut) begin
      $deposit(i_dut.i_rmw_buffer.i_shift_reg_gated.gen_shift_reg.data_q[NumRMWCuts-1],
               i_dut.i_rmw_buffer.i_shift_reg_gated.gen_shift_reg.data_q[NumRMWCuts-1] ^
               flip_cut_mask);
    end
  end

  /*******************
   *  Directed tests  *
   *******************/

  typedef enum {
    FlipNone, FlipSram, FlipCut, FlipWdata
  } flip_e;

  localparam prot_t OneBit  = prot_t'(1) << 5;
  localparam prot_t TwoBits = (prot_t'(1) << 3) | (prot_t'(1) << 36);

  // Issue one request and flip `mask` at `flip`. Returns the cycle of the grant and the read data.
  task automatic directed_req(input logic we_, input addr_t addr_, input data_t wdata_,
                              input be_t be_, input flip_e flip,
                              input prot_t mask, output longint unsigned gnt_cycle,
                              output data_t rdata_, output logic [1:0] rdata_error_);
    req        = 1'b1;
    we         = we_;
    addr       = addr_;
    wdata      = wdata_;
    be         = be_;
    wdata_flip = (flip == FlipWdata) ? mask : '0;
    to_test_time();
    while (!gnt) begin
      @(posedge clk);
      #TestTime;
    end
    gnt_cycle = cycle;
    next_cycle();
    req        = 1'b0;
    wdata_flip = '0;
    // The read data is in the SRAM output register BankAccessLatency cycles after the grant, and
    // in the last cut stage NumRMWCuts cycles later
    repeat (BankAccessLatency - 1) next_cycle();
    if (flip == FlipSram) flip_sram_rdata(mask);
    to_test_time();
    rdata_       = rdata;
    rdata_error_ = rdata_error;
    #(CyclTime - TestTime + ApplTime);
    if (flip == FlipCut) begin
      repeat (NumRMWCuts - 1) next_cycle();
      flip_cut_mask = mask;
      ->flip_cut;
    end
    // Let a read-modify-write finish
    repeat (NumRMWCuts + 2) next_cycle();
  endtask : directed_req

  // Check the error flags reported since the last call
  task automatic check_flags(string name, longint unsigned exp_cycle, logic exp_single,
                             logic exp_multi);
    automatic bit expected = exp_single || exp_multi;
    test_cnt++;
    if (flag_queue.size() != (expected ? 1 : 0)) begin
      $warning("ERROR! %s: expected %0d error reports, found %0d.", name, expected ? 1 : 0,
               flag_queue.size());
      error_cnt++;
    end else if (expected && (flag_queue[0].cycle != exp_cycle ||
                              flag_queue[0].single != exp_single ||
                              flag_queue[0].multi != exp_multi)) begin
      $warning("ERROR! %s: expected single %0b multi %0b in cycle %0d, found %0b %0b in %0d.",
               name, exp_single, exp_multi, exp_cycle, flag_queue[0].single, flag_queue[0].multi,
               flag_queue[0].cycle);
      error_cnt++;
    end
    flag_queue.delete();
  endtask : check_flags

  task automatic check_data(string name, data_t exp, data_t act);
    test_cnt++;
    if (act !== exp) begin
      $warning("ERROR! %s: expected 0x%h, found 0x%h.", name, exp, act);
      error_cnt++;
    end
  endtask : check_data

  // Write `init`, then do `op` on it with `mask` flipped at `flip`, and read the word back.
  task automatic directed_test(string name, addr_t addr_, data_t init, logic op_we,
                               data_t op_wdata, be_t op_be, flip_e flip, prot_t mask);
    automatic longint unsigned gnt_cycle, exp_cycle;
    automatic data_t           rdata_, expected;
    automatic logic [1:0]      rdata_error_;
    automatic logic            rmw, single, multi, checked;

    directed_req(1'b1, addr_, init, '1, FlipNone, '0, gnt_cycle, rdata_, rdata_error_);
    flag_queue.delete();

    directed_req(op_we, addr_, op_wdata, op_be, flip, mask, gnt_cycle, rdata_, rdata_error_);
    rmw       = op_we && (op_be != '1);
    exp_cycle = gnt_cycle + BankAccessLatency + (rmw ? NumRMWCuts : 0);
    single    = (mask == OneBit);
    multi     = (mask == TwoBits);
    // Plain reads in InputECC mode return the codeword unchecked
    checked   = (flip != FlipNone) && (rmw || !InputECC);
    check_flags({name, ": flags"}, exp_cycle, checked && single, checked && multi);
    if (!op_we && InputECC) begin
      check_data({name, ": tb-side ECC error"}, data_t'({multi, single}), data_t'(rdata_error_));
    end
    if (!op_we && !multi) check_data({name, ": read data"}, init, rdata_);

    // An uncorrectable error is written back with fresh ECC, the data is not predictable then
    expected = op_we ? apply_write(init, op_wdata, op_be) : init;
    directed_req(1'b0, addr_, '0, '0, FlipNone, '0, gnt_cycle, rdata_, rdata_error_);
    check_flags({name, ": readback flags"}, '0, 1'b0, 1'b0);
    if (!(rmw && multi)) check_data({name, ": readback"}, expected, rdata_);
    check_data({name, ": readback tb-side ECC error"}, '0, data_t'(rdata_error_));
  endtask : directed_test

  task automatic run_directed();
    automatic data_t init = 32'h7f80_1234;
    automatic data_t add  = 32'h0181_ff40;

    directed_test("read",                  8'h10, init, 1'b0, '0,  '0,   FlipNone, '0);
    directed_test("read, 1b SRAM flip",    8'h11, init, 1'b0, '0,  '0,   FlipSram, OneBit);
    directed_test("read, 2b SRAM flip",    8'h12, init, 1'b0, '0,  '0,   FlipSram, TwoBits);
    directed_test("write",                 8'h20, init, 1'b1, add, 4'hf, FlipNone, '0);
    directed_test("RMW",                   8'h30, init, 1'b1, add, 4'h6, FlipNone, '0);
    directed_test("RMW, 1b SRAM flip",     8'h31, init, 1'b1, add, 4'h6, FlipSram, OneBit);
    directed_test("RMW, 2b SRAM flip",     8'h32, init, 1'b1, add, 4'h6, FlipSram, TwoBits);
    if (NumRMWCuts > 0) begin
      directed_test("RMW, 1b cut flip",    8'h33, init, 1'b1, add, 4'h6, FlipCut,  OneBit);
      directed_test("RMW, 2b cut flip",    8'h34, init, 1'b1, add, 4'h6, FlipCut,  TwoBits);
    end
    if (InputECC) begin
      directed_test("RMW, 1b wdata flip",  8'h35, init, 1'b1, add, 4'h6, FlipWdata, OneBit);
    end
  endtask : run_directed

  // Read every word back after the hardware initialization. Zero data without any ECC error, on
  // the DUT flags or on the testbench-side decoder, means the stored codeword is all zeros.
  task automatic check_hw_init();
    automatic longint unsigned gnt_cycle;
    automatic data_t           rdata_;
    automatic logic [1:0]      rdata_error_;

    for (int unsigned i = 0; i < BankSize; i++) begin
      directed_req(1'b0, addr_t'(i), '0, '0, FlipNone, '0, gnt_cycle, rdata_, rdata_error_);
      check_data($sformatf("hw init 0x%02h: read data", i), '0, rdata_);
      check_data($sformatf("hw init 0x%02h: tb-side ECC error", i), '0, data_t'(rdata_error_));
      check_flags($sformatf("hw init 0x%02h: flags", i), '0, 1'b0, 1'b0);
    end
  endtask : check_hw_init

  /****************
   *  Test Bench  *
   ****************/

  task automatic run_apply();
    // Apply stimuli and collect results cycle
    forever begin
      apply_stimuli();
      repeat ($urandom_range(0,5)) next_cycle();
    end
  endtask : run_apply

  initial begin : watchdog
    #(CyclTime * (longint'(NoReq) * 10 + 10000));
    $fatal(1, "Timeout after %0d tests.", test_cnt);
  end : watchdog

  initial begin : tb
    // Initialize variables
    test_cnt     = '0;
    error_cnt    = '0;
    cycle        = '0;
    random_phase = 1'b0;

    for (int i = 0; i < BankSize; i++) begin
      memory[i] = '0;
    end

    req        = 1'b0;
    wdata      = '0;
    we         = '0;
    addr       = '0;
    be         = '0;
    wdata_flip = '0;
    hw_init    = HwInitEnabled;
    @(posedge rst_n)
    repeat(10) @(posedge clk);
    #ApplTime;
    hw_init = 1'b0;

    if (HwInitEnabled) check_hw_init();

    random_phase = 1'b1;
    fork
      run_apply();
      run_collect();
      fork
        generate_stimuli();
        check_result();
      join
    join_any
    disable fork;

    // Let the last request finish
    random_phase = 1'b0;
    req = 1'b0;
    repeat (BankAccessLatency + NumRMWCuts + 2) next_cycle();
    run_directed();

    $display("InputECC %0d NumRMWCuts %0d BankAccessLatency %0d HwInitEnabled %0d",
             InputECC, NumRMWCuts, BankAccessLatency, HwInitEnabled);
    $display("Checked %0d tests, found %0d mismatches.", test_cnt, error_cnt);
    if (error_cnt) $fatal(1, "Found %0d mismatches.", error_cnt);
    $finish();
  end : tb

endmodule
