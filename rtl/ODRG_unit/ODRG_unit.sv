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
// configurable Triple-Core Lock-Step unit

// Peripheral communication signals


module ODRG_unit #(
  parameter int unsigned InstrRdataWidth  = 32,
  parameter int unsigned NExtPerfCounters = 5,
  parameter int unsigned DataWidth        = 32,
  parameter int unsigned BEWidth          = 4,
  parameter int unsigned UserWidth        = 0,
  parameter type         odrg_req_t       = logic,
  parameter type         odrg_rsp_t       = logic
) (
  input  logic                             clk_i,
  input  logic                             rst_ni,

  input  odrg_req_t                        speriph_request,
  output odrg_rsp_t                        speriph_response,

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
  output logic [2:0][       UserWidth-1:0] intc_data_user_o,
  output logic [2:0][         BEWidth-1:0] intc_data_be_o,
  input  logic [2:0]                       intc_data_gnt_i,
  input  logic [2:0]                       intc_data_r_opc_i,
  input  logic [2:0][       DataWidth-1:0] intc_data_r_rdata_i,
  input  logic [2:0][       UserWidth-1:0] intc_data_r_user_i,
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
  input  logic [2:0][       UserWidth-1:0] core_data_user_i,
  input  logic [2:0][         BEWidth-1:0] core_data_be_i,
  output logic [2:0]                       core_data_gnt_o,
  output logic [2:0]                       core_data_r_opc_o,
  output logic [2:0][       DataWidth-1:0] core_data_r_rdata_o,
  output logic [2:0][       UserWidth-1:0] core_data_r_user_o,
  output logic [2:0]                       core_data_r_valid_o,

  output logic [2:0][NExtPerfCounters-1:0] core_perf_counters_o

  // APU/SHARED_FPU not implemented
);
  import odrg_manager_reg_pkg::* ;
  odrg_manager_reg2hw_t reg2hw;
  odrg_manager_hw2reg_t hw2reg;

  // State signals
  typedef enum logic [1:0] {NON_TMR, TMR_RUN, TMR_UNLOAD, TMR_RELOAD} redundancy_mode_e;

  redundancy_mode_e red_mode_d, red_mode_q;

  // TMR signals
  logic       TMR_error, main_error, data_error;
  logic [2:0] TMR_error_detect, main_error_cba, data_error_cba;

  localparam MAIN_TMR_WIDTH = 1   + 1      + 5         + 1        + 32        + 1;
  //                          busy  irq_ack  irq_ack_id  instr_req  instr_addr  data_req
  logic      [MAIN_TMR_WIDTH-1:0] main_tmr_out;
  logic [2:0][MAIN_TMR_WIDTH-1:0] main_tmr_in;

  localparam DATA_TMR_WIDTH = 32      + 1       + DataWidth + BEWidth + UserWidth;
  //                          data_add  data_wen  data_wdata  data_be   data_user
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
  logic [UserWidth-1:0] data_user;

  /************************************
   *  Slave Peripheral communication  *
   ************************************/

  odrg_manager_reg_top #(
    .reg_req_t ( odrg_req_t ),
    .reg_rsp_t ( odrg_rsp_t )
  ) i_registers (
    .clk_i     ( clk_i            ),
    .rst_ni    ( rst_ni           ),
    .reg_req_i ( speriph_request  ),
    .reg_rsp_o ( speriph_response ),
    .reg2hw    ( reg2hw           ),
    .hw2reg    ( hw2reg           ),
    .devmode_i ( '0               )
  );

  assign hw2reg.sp_store.d = '0;
  assign hw2reg.sp_store.de = '0;
  assign hw2reg.mismatches_0.d = reg2hw.mismatches_0.q + 1;
  assign hw2reg.mismatches_1.d = reg2hw.mismatches_1.q + 1;
  assign hw2reg.mismatches_2.d = reg2hw.mismatches_2.q + 1;

  /****************
   *  TMR Voters  *
   ****************/
  // TMR voters are separated for data, as this only needs to be compared when the core reads or writes data

  for (genvar i = 0; i < 3; i++) begin
    assign main_tmr_in[i] = {core_core_busy_i[i], core_irq_ack_i[i], core_irq_ack_id_i[i],
        core_instr_req_i[i], core_instr_addr_i[i], core_data_req_i[i]};
  end

  assign { core_busy, irq_ack, irq_ack_id,
      instr_req, instr_addr, data_req } = main_tmr_out;

  bitwise_TMR_voter #(
    .DataWidth( MAIN_TMR_WIDTH ),
    .VoterType( 0              )
  ) main_voter (
    .a_i         ( main_tmr_in[0] ),
    .b_i         ( main_tmr_in[1] ),
    .c_i         ( main_tmr_in[2] ),
    .majority_o  ( main_tmr_out   ),
    .error_o     ( main_error     ),
    .error_cba_o ( main_error_cba )
  );

  for (genvar i = 0; i < 3; i++) begin
    if (UserWidth > 0) begin
      assign data_tmr_in[i] = {core_data_add_i[i], core_data_wen_i[i], core_data_wdata_i[i], core_data_be_i[i], core_data_user_i[i]};
    end else begin
      assign data_tmr_in[i] = {core_data_add_i[i], core_data_wen_i[i], core_data_wdata_i[i], core_data_be_i[i]};
    end
  end

  if (UserWidth > 0) begin
    assign {data_add, data_wen, data_wdata, data_be, data_user} = data_tmr_out;
  end else begin
    assign {data_add, data_wen, data_wdata, data_be} = data_tmr_out;
    assign data_user = '0;
  end

  bitwise_TMR_voter #(
    .DataWidth( DATA_TMR_WIDTH ),
    .VoterType( 0              )
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

  /***********************
   *  FSM for ODRG unit  *
   ***********************/

  always_comb begin : proc_fsm
    red_mode_d = red_mode_q;
    hw2reg.mismatches_0.de = 1'b0;
    hw2reg.mismatches_1.de = 1'b0;
    hw2reg.mismatches_2.de = 1'b0;
    if (red_mode_q == TMR_RUN && TMR_error_detect != 3'b000) begin
      $display("[ODRG] %t - mismatch detected", $realtime);
      if (TMR_error_detect == 3'b001) hw2reg.mismatches_0.de = 1'b1;
      if (TMR_error_detect == 3'b010) hw2reg.mismatches_1.de = 1'b1;
      if (TMR_error_detect == 3'b100) hw2reg.mismatches_2.de = 1'b1;

      if (reg2hw.mode.restore_mode == 0) begin
        red_mode_d = TMR_UNLOAD;
      end
    end
    if (red_mode_q == TMR_UNLOAD) begin
      if (reg2hw.sp_store != '0) begin
        red_mode_d = TMR_RELOAD;
      end
    end
    if (red_mode_q == TMR_RELOAD) begin
      if (reg2hw.sp_store == '0) begin
        $display("[ODRG] %t - mismatch restored", $realtime);
        red_mode_d = TMR_RUN;
      end
    end

    // Before core startup: set TMR mode from reg2hw.mode.mode
    if (intc_fetch_en_i[0] == 0 & core_core_busy_i[0] == 0) begin
      if (reg2hw.mode.mode == 1) begin
        red_mode_d = TMR_RUN;
      end else begin
        red_mode_d = NON_TMR;
      end
    end

    // Assign reset signals - If reset should be triggered in during resynchronization, signal synchronization needs to be ensured.
    for (int i = 0; i < 3; i++) begin
      core_rst_no[i] = rst_ni;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_red_mode
    if(!rst_ni) begin
      red_mode_q <= NON_TMR;
    end else begin
      red_mode_q <= red_mode_d;
    end
  end

  /***********************************************
   *  IRQ MUX - with re-synchronization Trigger  *
   ***********************************************/

  always_comb begin : proc_irq_assign
    if (red_mode_q == NON_TMR) begin
      for (int i = 0; i < 3; i++) begin
        intc_irq_ack_o[i]    = core_irq_ack_i[i];
        intc_irq_ack_id_o[i] = core_irq_ack_id_i[i];

        core_irq_req_o[i] = intc_irq_req_i[i];
        core_irq_id_o[i]  = intc_irq_id_i[i];
      end
    end else begin
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

      // Trigger Re-synchronization
      if (red_mode_q == TMR_UNLOAD) begin
        for (int i = 0; i < 3; i++) begin
          core_irq_req_o[i] = 1'b1;
          core_irq_id_o[i]  = 5'd31;
        end
        intc_irq_ack_o[0] = '0;
        intc_irq_ack_id_o[0] = '0;
      end
    end
  end

  /*********************
   *  CTRL signal MUX  *
   *********************/

  always_comb begin : proc_ctrl_assign
    if (red_mode_q == NON_TMR) begin
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
        core_core_id_o[i]          = intc_core_id_i[0];
        core_cluster_id_o[i]       = intc_cluster_id_i[0];

        core_clock_en_o[i]         = intc_clock_en_i[0];
        core_fetch_en_o[i]         = intc_fetch_en_i[0]; // May need config on state transition
        core_boot_addr_o[i]        = intc_boot_addr_i[0]; // May need special value when restoring from tcls error
        core_debug_req_o[i]        = intc_debug_req_i[0];

        core_perf_counters_o[i]    = intc_perf_counters_i[0];
      end
    end
  end

  /******************
   *  Data bus MUX  *
   ******************/

  always_comb begin : proc_data_assign
    for (int i = 0; i < 3; i++) begin
      intc_data_add_o[i]    = core_data_add_i[i];
      intc_data_wen_o[i]    = core_data_wen_i[i];
      intc_data_wdata_o[i]  = core_data_wdata_i[i];
      intc_data_user_o[i]   = core_data_user_i[i];
      intc_data_be_o[i]     = core_data_be_i[i];
    end
    if (red_mode_q == NON_TMR) begin
      for (int i = 0; i < 3; i++) begin
        intc_data_req_o[i]    = core_data_req_i[i];

        core_data_gnt_o[i]     = intc_data_gnt_i[i];
        core_data_r_rdata_o[i] = intc_data_r_rdata_i[i];
        core_data_r_user_o[i]  = intc_data_r_user_i[i];
        core_data_r_opc_o[i]   = intc_data_r_opc_i[i];
        core_data_r_valid_o[i] = intc_data_r_valid_i[i];
      end
    end else begin
      intc_data_req_o[0]    = data_req;
      intc_data_add_o[0]    = data_add;
      intc_data_wen_o[0]    = data_wen;
      intc_data_wdata_o[0]  = data_wdata;
      intc_data_user_o[0]   = data_user;
      intc_data_be_o[0]     = data_be;
      
      intc_data_req_o[1]    = '0;
      intc_data_req_o[2]    = '0;

      for (int i = 0; i < 3; i++) begin
        core_data_gnt_o[i]     = intc_data_gnt_i[0];
        core_data_r_rdata_o[i] = intc_data_r_rdata_i[0];
        core_data_r_user_o[i]  = intc_data_r_user_i[0];
        core_data_r_opc_o[i]   = intc_data_r_opc_i[0];
        core_data_r_valid_o[i] = intc_data_r_valid_i[0];
      end
    end
  end

  /*******************
   *  INSTR bus MUX  *
   *******************/

  always_comb begin : proc_instr_assign
    for (int i = 0; i < 3; i++) begin
      intc_instr_addr_o[i] = core_instr_addr_i[i];
    end
    if (red_mode_q == NON_TMR) begin
      for (int i = 0; i < 3; i++) begin
        intc_instr_req_o[i]  = core_instr_req_i[i];

        core_instr_gnt_o[i]     = intc_instr_gnt_i[i];
        core_instr_r_rdata_o[i] = intc_instr_r_rdata_i[i];
        core_instr_r_valid_o[i] = intc_instr_r_valid_i[i];
      end
    end else begin
      intc_instr_req_o[0]  = instr_req;
      intc_instr_addr_o[0] = instr_addr;

      intc_instr_req_o[1]  = '0;
      intc_instr_req_o[2]  = '0;
      for (int i = 0; i < 3; i++) begin
        core_instr_gnt_o[i]     = intc_instr_gnt_i[0];
        core_instr_r_rdata_o[i] = intc_instr_r_rdata_i[0];
        core_instr_r_valid_o[i] = intc_instr_r_valid_i[0];
      end
    end
  end


endmodule
