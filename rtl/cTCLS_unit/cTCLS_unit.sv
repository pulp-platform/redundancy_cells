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
// configurable Tripli-Core Lock-Step unit

`include "register_interface/typedef.svh"

module cTCLS_unit #(
  parameter int unsigned InstrRdataWidth  = 32,
  parameter int unsigned NExtPerfCounters = 5,
  parameter int unsigned DataWidth        = 32,
  parameter int unsigned BEWidth          = 4,
  parameter int unsigned PeriphIDWidth    = 1
) (
  input  logic                             clk_i,
  input  logic                             rst_ni,

  input  logic                             periph_req_i,
  input  logic      [                31:0] periph_addr_i,
  input  logic                             periph_wen_i,
  input  logic      [                31:0] periph_wdata_i,
  input  logic      [                 3:0] periph_be_i,
  input  logic      [   PeriphIDWidth-1:0] periph_id_i,

  output logic                             periph_gnt_o,
  output logic                             periph_r_valid_o,
  output logic                             periph_r_opc_o,
  output logic      [   PeriphIDWidth-1:0] periph_r_id_o,
  output logic      [                31:0] periph_rdata_o,

  // Ports to connect Interconnect/rest of system
  input  logic [2:0][                 3:0] intc_core_id_i,
  input  logic [2:0][                 5:0] intc_cluster_id_i,

  input  logic [2:0]                       intc_clock_en_i,
  input  logic [2:0]                       intc_fetch_en_i,
  input  logic [2:0][                31:0] intc_boot_addr_i,
  output logic [2:0]                       intc_core_busy_o,

  input  logic [2:0]                       intc_irq_req_i,
  output logic [2:0]                       intc_irq_ack_o,
  input  logic [2:0][                 4:0] intc_irq_id_i,
  output logic [2:0][                 4:0] intc_irq_ack_id_o,

  output logic [2:0]                       intc_instr_req_o,
  input  logic [2:0]                       intc_instr_gnt_i,
  output logic [2:0][                31:0] intc_instr_addr_o,
  input  logic [2:0][ InstrRdataWidth-1:0] intc_instr_r_rdata_i,
  input  logic [2:0]                       intc_instr_r_valid_i,

  input  logic [2:0]                       intc_debug_req_i,

  output logic [2:0]                       intc_data_req_o,
  output logic [2:0][                31:0] intc_data_add_o,
  output logic [2:0]                       intc_data_wen_o,
  output logic [2:0][       DataWidth-1:0] intc_data_wdata_o,
  output logic [2:0][         BEWidth-1:0] intc_data_be_o,
  input  logic [2:0]                       intc_data_gnt_i,
  input  logic [2:0]                       intc_data_r_opc_i,
  input  logic [2:0][       DataWidth-1:0] intc_data_r_rdata_i,
  input  logic [2:0]                       intc_data_r_valid_i,

  input  logic [2:0][NExtPerfCounters-1:0] intc_perf_counters_i,

  // Ports to connect Cores
  output logic [2:0]                       core_rst_no,

  output logic [2:0][                 3:0] core_core_id_o,
  output logic [2:0][                 5:0] core_cluster_id_o,

  output logic [2:0]                       core_clock_en_o,
  output logic [2:0]                       core_fetch_en_o,
  output logic [2:0][                31:0] core_boot_addr_o,
  input  logic [2:0]                       core_core_busy_i,

  output logic [2:0]                       core_irq_req_o,
  input  logic [2:0]                       core_irq_ack_i,
  output logic [2:0][                 4:0] core_irq_id_o,
  input  logic [2:0][                 4:0] core_irq_ack_id_i,

  input  logic [2:0]                       core_instr_req_i,
  output logic [2:0]                       core_instr_gnt_o,
  input  logic [2:0][                31:0] core_instr_addr_i,
  output logic [2:0][ InstrRdataWidth-1:0] core_instr_r_rdata_o,
  output logic [2:0]                       core_instr_r_valid_o,

  output logic [2:0]                       core_debug_req_o,

  input  logic [2:0]                       core_data_req_i,
  input  logic [2:0][                31:0] core_data_add_i,
  input  logic [2:0]                       core_data_wen_i,
  input  logic [2:0][       DataWidth-1:0] core_data_wdata_i,
  input  logic [2:0][         BEWidth-1:0] core_data_be_i,
  output logic [2:0]                       core_data_gnt_o,
  output logic [2:0]                       core_data_r_opc_o,
  output logic [2:0][       DataWidth-1:0] core_data_r_rdata_o,
  output logic [2:0]                       core_data_r_valid_o,

  output logic [2:0][NExtPerfCounters-1:0] core_perf_counters_o

  // APU/SHARED_FPU not implemented
);
  
  import ctcls_manager_reg_pkg::* ;
  `REG_BUS_TYPEDEF_ALL(tcls, logic[31:0], logic[31:0], logic[3:0])

  tcls_req_t speriph_request;
  tcls_rsp_t speriph_response;
  ctcls_manager_reg2hw_t reg2hw;
  ctcls_manager_hw2reg_t hw2reg;

  typedef enum logic [1:0] {NORMAL, TMR, UNLOAD, RELOAD} redundancy_mode_e;

  redundancy_mode_e red_mode_d, red_mode_q;

  // TMR signals
  logic       TMR_error, main_error, data_error;
  logic [2:0] TMR_error_detect, main_error_cba, data_error_cba;

  localparam MAIN_TMR_WIDTH = 1   + 1      + 5         + 1        + 32        + 1;
  //                          busy  irq_ack  irq_ack_id  instr_req  instr_addr  data_req
  logic      [MAIN_TMR_WIDTH-1:0] main_tmr_out;
  logic [2:0][MAIN_TMR_WIDTH-1:0] main_tmr_in;

  localparam DATA_TMR_WIDTH = 32 + 1  + DataWidth + BEWidth;
  //                          add  wen  wdata       be
  logic      [DATA_TMR_WIDTH-1:0] data_tmr_out;
  logic [2:0][DATA_TMR_WIDTH-1:0] data_tmr_in;

  logic                 core_busy;

  logic                 irq_ack;
  logic [          4:0] irq_ack_id;

  logic                 instr_req;
  logic [         31:0] instr_addr;

  logic                 data_req;
  logic [         31:0] data_add;
  logic                 data_wen;
  logic [DataWidth-1:0] data_wdata;
  logic [  BEWidth-1:0] data_be;

  // Slave Peripheral communication 
  periph_to_reg #(
    .AW   (32),
    .DW   (DataWidth),
    .BW   (8),
    .IW   (PeriphIDWidth),
    .req_t(tcls_req_t),
    .rsp_t(tcls_rsp_t)
  ) i_periph_translate (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_i    (periph_req_i),
    .add_i    (periph_addr_i),
    .wen_i    (periph_wen_i),
    .wdata_i  (periph_wdata_i),
    .be_i     (periph_be_i),
    .id_i     (periph_id_i),
    .gnt_o    (periph_gnt_o),
    .r_rdata_o(periph_rdata_o),
    .r_opc_o  (periph_r_opc_o),
    .r_id_o   (periph_r_id_o),
    .r_valid_o(periph_r_valid_o),
    .reg_req_o(speriph_request),
    .reg_rsp_i(speriph_response)
  );

  ctcls_manager_reg_top #(
    .reg_req_t ( tcls_req_t ),
    .reg_rsp_t ( tcls_rsp_t )
  ) i_registers (
    .clk_i     ( clk_i            ),
    .rst_ni    ( rst_ni           ),
    .reg_req_i ( speriph_request  ),
    .reg_rsp_o ( speriph_response ),
    .reg2hw    ( reg2hw           ),
    .hw2reg    ( hw2reg           ),
    .devmode_i ( '0               )
  );

  assign hw2reg.mismatches_0.d = reg2hw.mismatches_0.q + 1;
  assign hw2reg.mismatches_1.d = reg2hw.mismatches_1.q + 1;
  assign hw2reg.mismatches_2.d = reg2hw.mismatches_2.q + 1;

  assign main_tmr_in[0] = {core_core_busy_i[0], core_irq_ack_i[0], core_irq_ack_id_i[0],
    core_instr_req_i[0], core_instr_addr_i[0], core_data_req_i[0]};
  assign main_tmr_in[1] = {core_core_busy_i[1], core_irq_ack_i[1], core_irq_ack_id_i[1],
    core_instr_req_i[1], core_instr_addr_i[1], core_data_req_i[1]};
  assign main_tmr_in[2] = {core_core_busy_i[2], core_irq_ack_i[2], core_irq_ack_id_i[2],
    core_instr_req_i[2], core_instr_addr_i[2], core_data_req_i[2]};

  assign { core_busy, irq_ack, irq_ack_id,
    instr_req, instr_addr, data_req } = main_tmr_out;

  bitwise_TMR_voter #(
    .DataWidth( MAIN_TMR_WIDTH ),
    .VoterType( 2              )
  ) main_voter (
    .a_i         ( main_tmr_in[0] ),
    .b_i         ( main_tmr_in[1] ),
    .c_i         ( main_tmr_in[2] ),
    .majority_o  ( main_tmr_out   ),
    .error_o     ( main_error     ),
    .error_cba_o ( main_error_cba )
  );


  assign data_tmr_in[0] = {core_data_add_i[0], core_data_wen_i[0], core_data_wdata_i[0], core_data_be_i[0]};
  assign data_tmr_in[1] = {core_data_add_i[1], core_data_wen_i[1], core_data_wdata_i[1], core_data_be_i[1]};
  assign data_tmr_in[2] = {core_data_add_i[2], core_data_wen_i[2], core_data_wdata_i[2], core_data_be_i[2]};

  assign {data_add, data_wen, data_wdata, data_be} = data_tmr_out;

  bitwise_TMR_voter #(
    .DataWidth(DATA_TMR_WIDTH),
    .VoterType(2)
  ) data_voter (
    .a_i         ( data_tmr_in[0] ),
    .b_i         ( data_tmr_in[1] ),
    .c_i         ( data_tmr_in[2] ),
    .majority_o  ( data_tmr_out   ),
    .error_o     ( data_error     ),
    .error_cba_o ( data_error_cba )
  );

  always_comb begin : proc_TMR_error
    TMR_error        = main_error;
    TMR_error_detect = main_error_cba;
    if (data_req) begin
      TMR_error        = main_error | data_error; // TODO: check for triple mismatch across both domains
      TMR_error_detect = main_error_cba | data_error_cba;
    end
  end

`ifdef TARGET_SIMULATION
  // initial force core_instr_req_i = 1'b1;
  always @(posedge clk_i) begin
    if (red_mode_q == TMR && TMR_error_detect != 3'b000) begin
      $display("ERROR_cba: 0b%3b\n", TMR_error_detect);
      $finish;
    end
  end
`endif

  always_comb begin : proc_fsm
    red_mode_d = red_mode_q;  // TODO: Implement FSM logic

    for (int i = 0; i < 3; i++) begin
      core_rst_no[i] = rst_ni;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_red_mode
    if(~rst_ni) begin
      red_mode_q <= NORMAL;
    end else begin
      red_mode_q <= red_mode_d;
    end
  end

  always_comb begin : proc_ctrl_assign
    if (red_mode_q == NORMAL) begin
      for (int i = 0; i < 3; i++) begin
        core_core_id_o[i]          = intc_core_id_i[i];
        core_cluster_id_o[i]       = intc_cluster_id_i[i];

        core_clock_en_o[i]         = intc_clock_en_i[i];
        core_fetch_en_o[i]         = intc_fetch_en_i[i]; // May need config on state transition
        core_boot_addr_o[i]        = intc_boot_addr_i[i];
        core_debug_req_o[i]        = intc_debug_req_i[i];

        core_perf_counters_o[i]    = intc_perf_counters_i[i];

        intc_core_busy_o[i] = core_core_busy_i[i];
      end
    end else begin
      intc_core_busy_o[0] = core_busy;
      intc_core_busy_o[1] = '0;
      intc_core_busy_o[2] = '0;

      for (int i = 0; i < 3; i++) begin
        core_core_id_o[i]          = intc_core_id_i[0]; // TODO: implement special logic for core_id?
        core_cluster_id_o[i]       = intc_cluster_id_i[0];

        core_clock_en_o[i]         = intc_clock_en_i[0];
        core_fetch_en_o[i]         = intc_fetch_en_i[0]; // May need config on state transition
        core_boot_addr_o[i]        = intc_boot_addr_i[0]; // May need special value when restoring from tcls error
        core_debug_req_o[i]        = intc_debug_req_i[0];

        core_perf_counters_o[i]    = intc_perf_counters_i[0];
      end
    end
  end

  always_comb begin : proc_data_assign
    if (red_mode_q == NORMAL) begin
      for (int i = 0; i < 3; i++) begin
        intc_data_req_o[i]    = core_data_req_i[i];
        intc_data_add_o[i]    = core_data_add_i[i];
        intc_data_wen_o[i]    = core_data_wen_i[i];
        intc_data_wdata_o[i]  = core_data_wdata_i[i];
        intc_data_be_o[i]     = core_data_be_i[i];

        core_data_gnt_o[i]     = intc_data_gnt_i[i];
        core_data_r_rdata_o[i] = intc_data_r_rdata_i[i];
        core_data_r_opc_o[i]   = intc_data_r_opc_i[i];
        core_data_r_valid_o[i] = intc_data_r_valid_i[i];
      end
    end else begin
      intc_data_req_o[0]    = data_req;
      intc_data_add_o[0]    = data_add;
      intc_data_wen_o[0]    = data_wen;
      intc_data_wdata_o[0]  = data_wdata;
      intc_data_be_o[0]     = data_be;
      
      intc_data_req_o[1]    = '0;
      intc_data_add_o[1]    = '0;
      intc_data_wen_o[1]    = '0;
      intc_data_wdata_o[1]  = '0;
      intc_data_be_o[1]     = '0;

      intc_data_req_o[2]    = '0;
      intc_data_add_o[2]    = '0;
      intc_data_wen_o[2]    = '0;
      intc_data_wdata_o[2]  = '0;
      intc_data_be_o[2]     = '0;

      for (int i = 0; i < 3; i++) begin
        core_data_gnt_o[i]     = intc_data_gnt_i[0];
        core_data_r_rdata_o[i] = intc_data_r_rdata_i[0];
        core_data_r_opc_o[i]   = intc_data_r_opc_i[0];
        core_data_r_valid_o[i] = intc_data_r_valid_i[0];
      end
    end
  
  end

  always_comb begin : proc_irq_assign
    if (red_mode_q == NORMAL) begin
      for (int i = 0; i < 3; i++) begin
        intc_irq_ack_o[i]    = core_irq_ack_i[i];
        intc_irq_ack_id_o[i] = core_irq_ack_id_i[i];

        core_irq_req_o[i] = intc_irq_req_i[i];
        core_irq_id_o[i]  = intc_irq_id_i[i];
      end
    end else begin
      // TODO: Add irq to trigger re-synchronization
      intc_irq_ack_o[0]    = irq_ack;
      intc_irq_ack_id_o[0] = irq_ack_id;

      intc_irq_ack_o[1] = '0;
      intc_irq_ack_o[2] = '0;
      intc_irq_ack_id_o[1] = '0;
      intc_irq_ack_id_o[2] = '0;
      for (int i = 0; i < 3; i++) begin
        core_irq_req_o[i] = intc_irq_req_i[0];
        core_irq_id_o[i]  = intc_irq_req_i[0];
      end
    end

  end

  always_comb begin : proc_instr_assign
    if (red_mode_q == NORMAL) begin
      for (int i = 0; i < 3; i++) begin
        intc_instr_req_o[i]  = core_instr_req_i[i];
        intc_instr_addr_o[i] = core_instr_addr_i[i];

        core_instr_gnt_o[i]     = intc_instr_gnt_i[i];
        core_instr_r_rdata_o[i] = intc_instr_r_rdata_i[i];
        core_instr_r_valid_o[i] = intc_instr_r_valid_i[i];
      end
    end else begin
      intc_instr_req_o[0]  = instr_req;
      intc_instr_addr_o[0] = instr_addr;

      intc_instr_req_o[1]  = '0;
      intc_instr_req_o[2]  = '0;
      intc_instr_addr_o[1] = '0;
      intc_instr_addr_o[2] = '0;
      for (int i = 0; i < 3; i++) begin
        core_instr_gnt_o[i]     = intc_instr_gnt_i[0];
        core_instr_r_rdata_o[i] = intc_instr_r_rdata_i[0];
        core_instr_r_valid_o[i] = intc_instr_r_valid_i[0];
      end
    end
  end


endmodule
