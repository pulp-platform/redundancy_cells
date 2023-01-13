// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Hybrid modular redundancy wrapping unit

module HMR_wrap #(
  parameter int unsigned NumCores       = 0,
  parameter bit          DMRSupported   = 1'b1,
  parameter bit          DMRFixed       = 1'b0,
  parameter bit          TMRSupported   = 1'b1,
  parameter bit          TMRFixed       = 1'b0,
  parameter bit          SeparateData   = 1'b1,
  parameter bit          BackupRegfile  = 1'b0,
  parameter bit          InterleaveGrps = 1'b1, // alternative is sequential grouping

  parameter int unsigned InstrDataWidth = 32,
  parameter int unsigned DataWidth      = 32,
  parameter int unsigned BeWidth        = 4,
  parameter int unsigned UserWidth      = 0,
  parameter int unsigned NumExtPerf     = 5,

  parameter type         reg_req_t      = logic,
  parameter type         reg_resp_t     = logic,
  parameter int unsigned NumTMRGroups   = NumCores/3,
  parameter int unsigned NumTMRCores    = NumTMRGroups * 3,
  parameter int unsigned NumTMRLeftover = NumCores - NumTMRCores,
  parameter int unsigned NumDMRGroups   = NumCores/2,
  parameter int unsigned NumDMRCores    = NumDMRGroups * 2,
  parameter int unsigned NumDMRLeftover = NumCores - NumDMRCores,
  parameter int unsigned NumSysCores    = DMRFixed ? NumDMRGroups : TMRFixed ? NumTMRCores : NumCores
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  // Port to configuration unit
  input  reg_req_t  reg_request_i,
  output reg_resp_t reg_response_o,

  // TMR signals
  output logic [NumTMRGroups-1:0] tmr_failure_o,
  output logic [ NumSysCores-1:0] tmr_error_o,
  output logic [NumTMRGroups-1:0] tmr_resynch_req_o,
  input  logic [NumTMRGroups-1:0] tmr_cores_synch_i,

  // TODO other required signals

  // Ports connecting to System
  input  logic [NumSysCores-1:0][           3:0] sys_core_id_i,
  input  logic [NumSysCores-1:0][           5:0] sys_cluster_id_i,

  input  logic [NumSysCores-1:0]                 sys_clock_en_i,
  input  logic [NumSysCores-1:0]                 sys_fetch_en_i,
  input  logic [NumSysCores-1:0][          31:0] sys_boot_addr_i,
  output logic [NumSysCores-1:0]                 sys_core_busy_o,

  input  logic [NumSysCores-1:0]                 sys_irq_req_i,
  output logic [NumSysCores-1:0]                 sys_irq_ack_o,
  input  logic [NumSysCores-1:0][           4:0] sys_irq_id_i,
  output logic [NumSysCores-1:0][           4:0] sys_irq_ack_id_o,

  output logic [NumSysCores-1:0]                 sys_instr_req_o,
  input  logic [NumSysCores-1:0]                 sys_instr_gnt_i,
  output logic [NumSysCores-1:0][          31:0] sys_instr_addr_o,
  input  logic [NumSysCores-1:0][InstrDataWidth-1:0] sys_instr_r_rdata_i,
  input  logic [NumSysCores-1:0]                 sys_instr_r_valid_i,
  input  logic [NumSysCores-1:0]                 sys_instr_err_i,

  input  logic [NumSysCores-1:0]                 sys_debug_req_i,

  output logic [NumSysCores-1:0]                 sys_data_req_o,
  output logic [NumSysCores-1:0][          31:0] sys_data_add_o,
  output logic [NumSysCores-1:0]                 sys_data_wen_o,
  output logic [NumSysCores-1:0][ DataWidth-1:0] sys_data_wdata_o,
  output logic [NumSysCores-1:0][ UserWidth-1:0] sys_data_user_o,
  output logic [NumSysCores-1:0][   BeWidth-1:0] sys_data_be_o,
  input  logic [NumSysCores-1:0]                 sys_data_gnt_i,
  input  logic [NumSysCores-1:0]                 sys_data_r_opc_i,
  input  logic [NumSysCores-1:0][ DataWidth-1:0] sys_data_r_rdata_i,
  input  logic [NumSysCores-1:0][ UserWidth-1:0] sys_data_r_user_i,
  input  logic [NumSysCores-1:0]                 sys_data_r_valid_i,
  input  logic [NumSysCores-1:0]                 sys_data_err_i,

  input  logic [NumSysCores-1:0][NumExtPerf-1:0] sys_perf_counters_i,

  // Ports connecting to the cores
  output logic [   NumCores-1:0]                 core_setback_o,

  output logic [   NumCores-1:0][           3:0] core_core_id_o,
  output logic [   NumCores-1:0][           5:0] core_cluster_id_o,

  output logic [   NumCores-1:0]                 core_clock_en_o,
  output logic [   NumCores-1:0]                 core_fetch_en_o,
  output logic [   NumCores-1:0][          31:0] core_boot_addr_o,
  input  logic [   NumCores-1:0]                 core_core_busy_i,

  output logic [   NumCores-1:0]                 core_irq_req_o,
  input  logic [   NumCores-1:0]                 core_irq_ack_i,
  output logic [   NumCores-1:0][           4:0] core_irq_id_o,
  input  logic [   NumCores-1:0][           4:0] core_irq_ack_id_i,

  input  logic [   NumCores-1:0]                 core_instr_req_i,
  output logic [   NumCores-1:0]                 core_instr_gnt_o,
  input  logic [   NumCores-1:0][          31:0] core_instr_addr_i,
  output logic [   NumCores-1:0][InstrDataWidth-1:0] core_instr_r_rdata_o,
  output logic [   NumCores-1:0]                 core_instr_r_valid_o,
  output logic [   NumCores-1:0]                 core_instr_err_o,

  output logic [   NumCores-1:0]                 core_debug_req_o,

  input  logic [   NumCores-1:0]                 core_data_req_i,
  input  logic [   NumCores-1:0][          31:0] core_data_add_i,
  input  logic [   NumCores-1:0]                 core_data_wen_i,
  input  logic [   NumCores-1:0][ DataWidth-1:0] core_data_wdata_i,
  input  logic [   NumCores-1:0][ UserWidth-1:0] core_data_user_i,
  input  logic [   NumCores-1:0][   BeWidth-1:0] core_data_be_i,
  output logic [   NumCores-1:0]                 core_data_gnt_o,
  output logic [   NumCores-1:0]                 core_data_r_opc_o,
  output logic [   NumCores-1:0][ DataWidth-1:0] core_data_r_rdata_o,
  output logic [   NumCores-1:0][ UserWidth-1:0] core_data_r_user_o,
  output logic [   NumCores-1:0]                 core_data_r_valid_o,
  output logic [   NumCores-1:0]                 core_data_err_o,

  output logic [   NumCores-1:0][NumExtPerf-1:0] core_perf_counters_o

  // APU/SHARED_FPU not implemented
);

  if (TMRFixed && DMRFixed) $fatal(1, "Cannot fix both TMR and DMR!");

  typedef enum logic [1:0] {NON_TMR, TMR_RUN, TMR_UNLOAD, TMR_RELOAD} tmr_mode_e;
  localparam tmr_mode_e DefaultTMRMode = NON_TMR;

  localparam int unsigned CtrlConcatWidth = 1   + 1      + 5         + 1    + 32    + 1;
  //                                        busy  irq_ack  irq_ack_id  i_req  i_addr  d_req
  localparam int unsigned DataConcatWidth = 32      + 1       + DataWidth + BeWidth + UserWidth;
  //                                        data_add  data_wen  data_wdata  data_be   data_user
  localparam int unsigned MainConcatWidth = SeparateData ? CtrlConcatWidth : 
                                            CtrlConcatWidth + DataConcatWidth;

  logic [    NumCores-1:0][MainConcatWidth-1:0] main_concat_in;
  logic [NumTMRGroups-1:0][MainConcatWidth-1:0] main_tmr_out;
  logic [NumDMRGroups-1:0][MainConcatWidth-1:0] main_dmr_out;

  logic [    NumCores-1:0][DataConcatWidth-1:0] data_concat_in;
  logic [NumTMRGroups-1:0][DataConcatWidth-1:0] data_tmr_out;
  logic [NumDMRGroups-1:0][DataConcatWidth-1:0] data_dmr_out;

  logic [NumTMRGroups-1:0] tmr_failure, tmr_failure_main, tmr_failure_data;
  logic [NumTMRGroups-1:0][2:0] tmr_error, tmr_error_main, tmr_error_data;
  logic [NumTMRGroups-1:0] tmr_single_mismatch;

  logic [NumTMRGroups-1:0]                 tmr_core_busy_out;
  logic [NumTMRGroups-1:0]                 tmr_irq_ack_out;
  logic [NumTMRGroups-1:0][           4:0] tmr_irq_ack_id_out;
  logic [NumTMRGroups-1:0]                 tmr_instr_req_out;
  logic [NumTMRGroups-1:0][          31:0] tmr_instr_addr_out;
  logic [NumTMRGroups-1:0]                 tmr_data_req_out;
  logic [NumTMRGroups-1:0][          31:0] tmr_data_add_out;
  logic [NumTMRGroups-1:0]                 tmr_data_wen_out;
  logic [NumTMRGroups-1:0][ DataWidth-1:0] tmr_data_wdata_out;
  logic [NumTMRGroups-1:0][ UserWidth-1:0] tmr_data_user_out;
  logic [NumTMRGroups-1:0][   BeWidth-1:0] tmr_data_be_out;

  logic [NumDMRGroups-1:0]                 dmr_core_busy_out;
  logic [NumDMRGroups-1:0]                 dmr_irq_ack_out;
  logic [NumDMRGroups-1:0][           4:0] dmr_irq_ack_id_out;
  logic [NumDMRGroups-1:0]                 dmr_instr_req_out;
  logic [NumDMRGroups-1:0][          31:0] dmr_instr_addr_out;
  logic [NumDMRGroups-1:0]                 dmr_data_req_out;
  logic [NumDMRGroups-1:0][          31:0] dmr_data_add_out;
  logic [NumDMRGroups-1:0]                 dmr_data_wen_out;
  logic [NumDMRGroups-1:0][ DataWidth-1:0] dmr_data_wdata_out;
  logic [NumDMRGroups-1:0][ UserWidth-1:0] dmr_data_user_out;
  logic [NumDMRGroups-1:0][   BeWidth-1:0] dmr_data_be_out;

  for (genvar i = 0; i < NumCores; i++) begin : gen_concat
    if (SeparateData) begin
      assign main_concat_in[i] = {core_core_busy_i[i], core_irq_ack_i[i], core_irq_ack_id_i[i],
        core_instr_req_i[i], core_instr_addr_i[i], core_data_req_i[i]};
      assign data_concat_in[i] = {core_data_add_i[i], core_data_wen_i[i], core_data_wdata_i[i],
                               core_data_be_i[i], core_data_user_i[i]};
    end else begin
      assign main_concat_in[i] = {core_core_busy_i[i], core_irq_ack_i[i], core_irq_ack_id_i[i],
        core_instr_req_i[i], core_instr_addr_i[i], core_data_req_i[i], core_data_add_i[i], 
        core_data_wen_i[i], core_data_wdata_i[i], core_data_be_i[i], core_data_user_i[i]};
      assign data_concat_in = '0;
    end
  end

  /***************************
   *  HMR Control Registers  *
   ***************************/

  localparam NumRegPorts = 1 + (TMRSupported || TMRFixed ? NumTMRGroups : 0) + (DMRSupported || DMRFixed ? NumDMRGroups : 0);

  reg_req_t  [NumRegPorts-1:0] register_reqs;
  reg_resp_t [NumRegPorts-1:0] register_resps;

  reg_demux #(
    .NoPorts    ( NumRegPorts ),
    .req_t      ( reg_req_t    ),
    .rsp_t      ( reg_resp_t   )
  ) i_reg_demux (
    .clk_i,
    .rst_ni,
    .in_select_i( /* TODO */ ),
    .in_req_i   ( reg_request_i                         ),
    .in_rsp_o   ( reg_response_o                        ),
    .out_req_o  ( register_reqs                         ),
    .out_rsp_i  ( register_resps                        )
  );

  hmr_registers_reg_pkg::hmr_registers_hw2reg_t hmr_hw2reg;
  hmr_registers_reg_pkg::hmr_registers_reg2hw_t hmr_reg2hw;

  hmr_registers_reg_top #(
    .reg_req_t( reg_req_t  ),
    .reg_rsp_t( reg_resp_t )
  ) i_hmr_registers (
    .clk_i,
    .rst_ni,
    .hw2reg   (hmr_hw2reg),
    .reg2hw   (hmr_reg2hw),
    .reg_req_i(register_reqs[0] ),
    .reg_rsp_o(register_resps[0]),
    .devmode_i('0)
  );

  assign hmr_hw2reg.avail_config.independent.d = ~(TMRFixed | DMRFixed);
  // assign hmr_hw2reg.avail_config.independent.de = 1'b1;
  assign hmr_hw2reg.avail_config.dual.d = DMRFixed | DMRSupported;
  // assign hmr_hw2reg.avail_config.dual.de = 1'b1;
  assign hmr_hw2reg.avail_config.triple.d = TMRFixed | TMRSupported;
  // assign hmr_hw2reg.avail_config.triple.de = 1'b1;

  assign hmr_hw2reg.dmr_enable.d = '0;
  assign hmr_hw2reg.tmr_enable.d = '0;

  assign hmr_hw2reg.tmr_config.delay_resynch.d = '0;
  // assign hmr_hw2reg.tmr_config.delay_resynch.de = '0;
  // assign hmr_hw2reg.tmr_config.setback.de = '0;
  assign hmr_hw2reg.tmr_config.setback.d = '0;
  // assign hmr_hw2reg.tmr_config.reload_setback.de = '0;
  assign hmr_hw2reg.tmr_config.reload_setback.d  = '0;
  // assign hmr_hw2reg.tmr_config.force_resynch.de = '0;
  assign hmr_hw2reg.tmr_config.force_resynch.d = '0;


  /****************
   *  TMR Voters  *
   ****************/

  if (TMRSupported || TMRFixed) begin : gen_tmr_voters
    for (genvar i = 0; i < NumTMRGroups; i++) begin : gen_tmr_voter
      assign tmr_failure[i]         = tmr_data_req_out[i] ?
                          tmr_failure_main | tmr_failure_data : tmr_failure_main;
      assign tmr_error[i]      = tmr_data_req_out[i] ?
                          tmr_error_main[i] | tmr_error_data[i] : tmr_error_main[i];
      assign tmr_single_mismatch[i] = tmr_error[i] != 3'b000;

      bitwise_TMR_voter #(
        .DataWidth( MainConcatWidth ),
        .VoterType( 0 )
      ) i_main_voter (
        .a_i        ( main_concat_in[InterleaveGrps ? i                  : i*3  ] ),
        .b_i        ( main_concat_in[InterleaveGrps ? i +   NumTMRGroups : i*3+1] ),
        .c_i        ( main_concat_in[InterleaveGrps ? i + 2*NumTMRGroups : i*3+2] ),
        .majority_o ( main_tmr_out  [i    ] ),
        .error_o    ( tmr_failure_main[i]   ),
        .error_cba_o( tmr_error_main[i    ] )
      );
      if (SeparateData) begin : gen_data_voter
        bitwise_TMR_voter #(
          .DataWidth( DataConcatWidth ),
          .VoterType( 0 )
        ) i_main_voter (
          .a_i        ( data_concat_in[InterleaveGrps ? i                  : i*3  ] ),
          .b_i        ( data_concat_in[InterleaveGrps ? i +   NumTMRGroups : i*3+1] ),
          .c_i        ( data_concat_in[InterleaveGrps ? i + 2*NumTMRGroups : i*3+2] ),
          .majority_o ( data_tmr_out  [i    ] ),
          .error_o    ( tmr_failure_data[i]   ),
          .error_cba_o( tmr_error_data[i    ] )
        );

        assign {tmr_core_busy_out[i], tmr_irq_ack_out[i], tmr_irq_ack_id_out[i],
               tmr_instr_req_out[i], tmr_instr_addr_out[i], tmr_data_req_out[i]} = main_tmr_out[i];
        assign {tmr_data_add_out[i], tmr_data_wen_out[i], tmr_data_wdata_out[i],
               tmr_data_be_out[i], tmr_data_user_out[i]} = data_tmr_out[i];
      end else begin : gen_data_in_main
        assign tmr_failure_data[i] = 1'b0;
        assign tmr_error_data[i] = 3'b000;
        assign {tmr_core_busy_out[i], tmr_irq_ack_out[i], tmr_irq_ack_id_out[i],
               tmr_instr_req_out[i], tmr_instr_addr_out[i], tmr_data_req_out[i],
               tmr_data_add_out[i], tmr_data_wen_out[i], tmr_data_wdata_out[i],
               tmr_data_be_out[i], tmr_data_user_out[i]} = main_tmr_out[i];
      end
    end
    if (NumTMRLeftover > 0) begin : gen_tmr_leftover_error
      // assign tmr_error_main[NumCores-1-:NumTMRLeftover] = '0;
      // assign tmr_error_data[NumCores-1-:NumTMRLeftover] = '0;
      // assign tmr_error     [NumCores-1-:NumTMRLeftover] = '0;
    end
  end else begin : gen_no_tmr_voted
    assign tmr_error_main   = '0;
    assign tmr_error_data   = '0;
    assign tmr_error        = '0;
    assign tmr_failure_main = '0;
    assign tmr_failure_data = '0;
    assign tmr_failure      = '0;
    assign main_tmr_out = '0;
    assign data_tmr_out = '0;
    assign {tmr_core_busy_out, tmr_irq_ack_out, tmr_irq_ack_id_out,
           tmr_instr_req_out, tmr_instr_addr_out, tmr_data_req_out,
           tmr_data_add_out, tmr_data_wen_out, tmr_data_wdata_out,
           tmr_data_be_out, tmr_data_user_out} = '0;
  end

  // Assign output signals
  if (DMRSupported && TMRSupported) begin : gen_full_HMR
    if (TMRFixed || DMRFixed) $fatal(1, "Cannot support both TMR and DMR and fix one!");

    // TODO

  end else if (TMRSupported || TMRFixed) begin : gen_TMR_only
    if (TMRFixed && NumCores % 3 != 0) $warning("Extra cores added not properly handled!");
    tmr_mode_e [NumTMRGroups-1:0] red_mode_d, red_mode_q;

    import odrg_manager_reg_pkg::*;
    odrg_manager_reg2hw_t [NumTMRGroups-1:0] reg2hw;
    odrg_manager_hw2reg_t [NumTMRGroups-1:0] hw2reg;

    reg_req_t  [NumTMRGroups-1:0] tmr_req;
    reg_resp_t [NumTMRGroups-1:0] tmr_resp;

    logic [NumTMRGroups-1:0] setback_d;

    localparam TMRSelWidth = $clog2(NumTMRGroups);

    /*******************
     *  Register File  *
     *******************/
    // reg_demux #(
    //   .NoPorts    ( NumTMRGroups ),
    //   .req_t      ( reg_req_t    ),
    //   .rsp_t      ( reg_resp_t   )
    // ) i_reg_demux (
    //   .clk_i,
    //   .rst_ni,
    //   .in_select_i( reg_request_i.addr[8+TMRSelWidth-1:8] ),
    //   .in_req_i   ( reg_request_i                         ),
    //   .in_rsp_o   ( reg_response_o                        ),
    //   .out_req_o  ( tmr_req                               ),
    //   .out_rsp_i  ( tmr_resp                              )
    // );

    for (genvar i = 0; i < NumTMRGroups; i++) begin : gen_tmr_groups
      odrg_manager_reg_top #(
        .reg_req_t( reg_req_t ),
        .reg_rsp_t( reg_resp_t )
      ) i_registers (
        .clk_i,
        .rst_ni,
        .reg_req_i( register_reqs [1+i] ),
        .reg_rsp_o( register_resps[1+i] ),
        .reg2hw   ( reg2hw  [i] ),
        .hw2reg   ( hw2reg  [i] ),
        .devmode_i( 1'b0        )
      );

      assign hw2reg[i].mode.mode.d            = 1'b0;
      assign hw2reg[i].mode.mode.de           = 1'b0;
      assign hw2reg[i].mode.delay_resynch.d   = 1'b0;
      assign hw2reg[i].mode.delay_resynch.de  = 1'b0;
      assign hw2reg[i].mode.setback.d         = 1'b0;
      assign hw2reg[i].mode.setback.de        = 1'b0;
      assign hw2reg[i].mode.reload_setback.d  = 1'b0;
      assign hw2reg[i].mode.reload_setback.de = 1'b0;
      assign hw2reg[i].mode.force_resynch.d   = 1'b0;

      /***********************
       *  FSM for ODRG unit  *
       ***********************/
      always_comb begin : proc_fsm
        setback_d[i] = 1'b0;
        red_mode_d[i] = red_mode_q[i];
        hw2reg[i].mismatches_0.de = 1'b0;
        hw2reg[i].mismatches_1.de = 1'b0;
        hw2reg[i].mismatches_2.de = 1'b0;
        hw2reg[i].mode.force_resynch.de = 1'b0;

        // If forced execute resynchronization
        if (red_mode_q[i] == TMR_RUN && reg2hw[i].mode.force_resynch.q) begin
          hw2reg[i].mode.force_resynch.de = 1'b1;
          if (reg2hw[i].mode.delay_resynch == 0) begin
            red_mode_d[i] = TMR_UNLOAD;
            // TODO: buffer the restoration until delay_resynch is disabled
          end
        end

        // If error detected, do resynchronization
        if (red_mode_q[i] == TMR_RUN && tmr_single_mismatch[i]) begin
          $display("[ODRG] %t - mismatch detected", $realtime);
          if (tmr_error[i][0]) hw2reg[i].mismatches_0.de = 1'b1;
          if (tmr_error[i][1]) hw2reg[i].mismatches_1.de = 1'b1;
          if (tmr_error[i][2]) hw2reg[i].mismatches_2.de = 1'b1;

          if (reg2hw[i].mode.delay_resynch == 0) begin
            red_mode_d[i] = TMR_UNLOAD;
            // TODO: buffer the restoration until delay_resynch is disabled
          end
        end

        // If unload complete, go to reload (and reset)
        if (red_mode_q[i] == TMR_UNLOAD) begin
          if (reg2hw[i].sp_store.q != '0) begin
            red_mode_d[i] = TMR_RELOAD;
            if (reg2hw[i].mode.setback.q) begin
              setback_d[i] = 1'b1;
            end
          end
        end

        // If reload complete, finish (or reset if error happens during reload)
        if (red_mode_q[i] == TMR_RELOAD) begin
          if (reg2hw[i].sp_store == '0) begin
            $display("[ODRG] %t - mismatch restored", $realtime);
            red_mode_d[i] = TMR_RUN;
          end else begin
            if ((tmr_single_mismatch[i] || tmr_failure[i]) && reg2hw[i].mode.setback.q &&
                reg2hw[i].mode.reload_setback.q &&
                !(reg2hw[i].sp_store.qe && tmr_req[i].wdata == '0)) begin
              setback_d[i] = 1'b1;
            end
          end
        end

        // Before core startup: set TMR mode from reg2hw.mode.mode
        if (!TMRFixed) begin
          if (sys_fetch_en_i[InterleaveGrps ? i : 3*i] == 0 && core_core_busy_i[InterleaveGrps ? i : 3*i] == 0) begin
            if (reg2hw[i].mode.mode == 1) begin
              red_mode_d[i] = NON_TMR;
            end else begin
              red_mode_d[i] = TMR_RUN;
            end
          end
          // split single-error tolerant mode to performance mode anytime (but require correct core state)
          if (red_mode_q[i] == TMR_RUN) begin
            if (reg2hw[i].mode.mode == 1) begin
              red_mode_d[i] = NON_TMR;
            end
          end
          // Set TMR mode on external signal that cores are synchronized
          if (red_mode_q[i] == NON_TMR && tmr_cores_synch_i[i]) begin
            if (reg2hw[i].mode.mode == 0) begin
              red_mode_d[i] = TMR_RUN;
            end
          end
        end
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_red_mode
      if(!rst_ni) begin
        red_mode_q <= {NumTMRGroups{DefaultTMRMode}};
      end else begin
        red_mode_q <= red_mode_d;
      end
    end

    for (genvar i = 0; i < NumCores; i++) begin : gen_core_inputs
      localparam SysCoreIndex = TMRFixed ? i/3 : InterleaveGrps ? i%NumTMRGroups : i-(i%3);
      always_comb begin
        if (i < NumTMRCores && (TMRFixed || red_mode_q[InterleaveGrps ? i%NumTMRGroups : i/3] != NON_TMR)) begin : tmr_mode

          // CTRL
          core_core_id_o      [i] = sys_core_id_i      [SysCoreIndex];
          core_cluster_id_o   [i] = sys_cluster_id_i   [SysCoreIndex];

          core_clock_en_o     [i] = sys_clock_en_i     [SysCoreIndex];
          core_fetch_en_o     [i] = sys_fetch_en_i     [SysCoreIndex];
          core_boot_addr_o    [i] = sys_boot_addr_i    [SysCoreIndex];

          core_debug_req_o    [i] = sys_debug_req_i    [SysCoreIndex];
          core_perf_counters_o[i] = sys_perf_counters_i[SysCoreIndex];

          // IRQ
          core_irq_req_o      [i] = sys_irq_req_i      [SysCoreIndex];
          core_irq_id_o       [i] = sys_irq_id_i       [SysCoreIndex];

          // INSTR
          core_instr_gnt_o    [i] = sys_instr_gnt_i    [SysCoreIndex];
          core_instr_r_rdata_o[i] = sys_instr_r_rdata_i[SysCoreIndex];
          core_instr_r_valid_o[i] = sys_instr_r_valid_i[SysCoreIndex];
          core_instr_err_o    [i] = sys_instr_err_i    [SysCoreIndex];

          // DATA
          core_data_gnt_o     [i] = sys_data_gnt_i     [SysCoreIndex];
          core_data_r_opc_o   [i] = sys_data_r_opc_i   [SysCoreIndex];
          core_data_r_rdata_o [i] = sys_data_r_rdata_i [SysCoreIndex];
          core_data_r_user_o  [i] = sys_data_r_user_i  [SysCoreIndex];
          core_data_r_valid_o [i] = sys_data_r_valid_i [SysCoreIndex];
          core_data_err_o     [i] = sys_data_err_i     [SysCoreIndex];

        end else begin : independent_mode

          // CTRL
          core_core_id_o      [i] = sys_core_id_i      [i];
          core_cluster_id_o   [i] = sys_cluster_id_i   [i];

          core_clock_en_o     [i] = sys_clock_en_i     [i];
          core_fetch_en_o     [i] = sys_fetch_en_i     [i];
          core_boot_addr_o    [i] = sys_boot_addr_i    [i];

          core_debug_req_o    [i] = sys_debug_req_i    [i];
          core_perf_counters_o[i] = sys_perf_counters_i[i];

          // IRQ
          core_irq_req_o      [i] = sys_irq_req_i      [i];
          core_irq_id_o       [i] = sys_irq_id_i       [i];

          // INSTR
          core_instr_gnt_o    [i] = sys_instr_gnt_i    [i];
          core_instr_r_rdata_o[i] = sys_instr_r_rdata_i[i];
          core_instr_r_valid_o[i] = sys_instr_r_valid_i[i];
          core_instr_err_o    [i] = sys_instr_err_i    [i];

          // DATA
          core_data_gnt_o     [i] = sys_data_gnt_i     [i];
          core_data_r_opc_o   [i] = sys_data_r_opc_i   [i];
          core_data_r_rdata_o [i] = sys_data_r_rdata_i [i];
          core_data_r_user_o  [i] = sys_data_r_user_i  [i];
          core_data_r_valid_o [i] = sys_data_r_valid_i [i];
          core_data_err_o     [i] = sys_data_err_i     [i];

        end
      end
    end

    for (genvar i = 0; i < NumSysCores; i++) begin : gen_core_outputs
      localparam CoreCoreIndex = TMRFixed ? i : i/3;
      always_comb begin
        if ((TMRFixed && i < NumTMRGroups) || (i < NumTMRCores && red_mode_q[InterleaveGrps ? i%NumTMRGroups : i-(i%3)] != NON_TMR)) begin : tmr_mode
          if (TMRFixed || (InterleaveGrps && i < NumTMRGroups) || (!InterleaveGrps && i%3 == 0)) begin : is_tmr
            
            // CTRL
            sys_core_busy_o     [i] = tmr_core_busy_out[CoreCoreIndex];

            // IRQ
            sys_irq_ack_o       [i] = core_irq_ack_i   [CoreCoreIndex];
            sys_irq_ack_id_o    [i] = core_irq_ack_id_i[CoreCoreIndex];

            // INSTR
            sys_instr_req_o     [i] = core_instr_req_i [CoreCoreIndex];
            sys_instr_addr_o    [i] = core_instr_addr_i[CoreCoreIndex];

            // DATA
            sys_data_req_o      [i] = core_data_req_i  [CoreCoreIndex];
            sys_data_add_o      [i] = core_data_add_i  [CoreCoreIndex];
            sys_data_wen_o      [i] = core_data_wen_i  [CoreCoreIndex];
            sys_data_wdata_o    [i] = core_data_wdata_i[CoreCoreIndex];
            sys_data_user_o     [i] = core_data_user_i [CoreCoreIndex];
            sys_data_be_o       [i] = core_data_be_i   [CoreCoreIndex];

          end else begin : disable_core // Assign disable

            // CTLR
            sys_core_busy_o     [i] = '0;

            // IRQ
            sys_irq_ack_o       [i] = '0;
            sys_irq_ack_id_o    [i] = '0;

            // INSTR
            sys_instr_req_o     [i] = '0;
            sys_instr_addr_o    [i] = '0;

            // DATA
            sys_data_req_o      [i] = '0;
            sys_data_add_o      [i] = '0;
            sys_data_wen_o      [i] = '0;
            sys_data_wdata_o    [i] = '0;
            sys_data_user_o     [i] = '0;
            sys_data_be_o       [i] = '0;

          end
        end else begin : independent_mode
          // CTRL
          sys_core_busy_o     [i] = core_core_busy_i [i];

          // IRQ
          sys_irq_ack_o       [i] = core_irq_ack_i   [i];
          sys_irq_ack_id_o    [i] = core_irq_ack_id_i[i];

          // INSTR
          sys_instr_req_o     [i] = core_instr_req_i [i];
          sys_instr_addr_o    [i] = core_instr_addr_i[i];

          // DATA
          sys_data_req_o      [i] = core_data_req_i  [i];
          sys_data_add_o      [i] = core_data_add_i  [i];
          sys_data_wen_o      [i] = core_data_wen_i  [i];
          sys_data_wdata_o    [i] = core_data_wdata_i[i];
          sys_data_user_o     [i] = core_data_user_i [i];
          sys_data_be_o       [i] = core_data_be_i   [i];
        end
      end
    end

  end else if (DMRSupported || DMRFixed) begin : gen_DMR_only

    // TODO

  end else begin : gen_no_redundancy
    // Direct assignment, disable all
    assign core_setback_o       = '0;
    
    // CTRL
    assign core_core_id_o       = sys_core_id_i;
    assign core_cluster_id_o    = sys_cluster_id_i;

    assign core_clock_en_o      = sys_clock_en_i;
    assign core_fetch_en_o      = sys_fetch_en_i;
    assign core_boot_addr_o     = sys_boot_addr_i;
    assign sys_core_busy_o      = core_core_busy_i;
    
    assign core_debug_req_o     = sys_debug_req_i;
    assign core_perf_counters_o = sys_perf_counters_i;

    // IRQ
    assign core_irq_req_o       = sys_irq_req_i;
    assign sys_irq_ack_o        = core_irq_ack_i;
    assign core_irq_id_o        = sys_irq_id_i;
    assign sys_irq_ack_id_o     = core_irq_ack_id_i;

    // INSTR
    assign sys_instr_req_o      = core_instr_req_i;
    assign core_instr_gnt_o     = sys_instr_gnt_i;
    assign sys_instr_addr_o     = core_instr_addr_i;
    assign core_instr_r_rdata_o = sys_instr_r_rdata_i;
    assign core_instr_r_valid_o = sys_instr_r_valid_i;
    assign core_instr_err_o     = sys_instr_err_i;

    // DATA
    assign sys_data_req_o       = core_data_req_i;
    assign sys_data_add_o       = core_data_add_i;
    assign sys_data_wen_o       = core_data_wen_i;
    assign sys_data_wdata_o     = core_data_wdata_i;
    assign sys_data_user_o      = core_data_user_i;
    assign sys_data_be_o        = core_data_be_i;
    assign core_data_gnt_o      = sys_data_gnt_i;
    assign core_data_r_opc_o    = sys_data_r_opc_i;
    assign core_data_r_rdata_o  = sys_data_r_rdata_i;
    assign core_data_r_user_o   = sys_data_r_user_i;
    assign core_data_r_valid_o  = sys_data_r_valid_i;
    assign core_data_err_o      = sys_data_err_i;
  end

endmodule
