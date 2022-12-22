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
  parameter int unsigned NumCores     = 0,
  parameter bit          DMRSupported = 1'b1,
  parameter bit          DMRFixed     = 1'b0,
  parameter bit          TMRSupported = 1'b1,
  parameter bit          TMRFixed     = 1'b0,
  parameter bit          SeparateData = 1'b1,

  parameter int unsigned InstrDataWidth = 32,
  parameter int unsigned DataWidth      = 32,
  parameter int unsigned BeWidth        = 4,
  parameter int unsigned UserWidth      = 0,
  parameter int unsigned NumExtPerf     = 5,

  parameter type         reg_req_t    = logic,
  parameter type         reg_resp_t   = logic,
  parameter int unsigned NumSysCores  = DMRFixed ? NumCores/2 : TMRFixed ? NumCores/3 : NumCores
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  // Port to configuration unit
  input  reg_req_t  reg_request_i,
  output reg_resp_t reg_response_o

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

  localparam int unsigned NumTMRGroups   = NumCores/3;
  localparam int unsigned NumTMRCores    = NumTMRGroups * 3
  localparam int unsigned NumTMRLeftover = NumCores - NumTMRCores;
  localparam int unsigned NumDMRGroups   = NumCores/2;
  localparam int unsigned NumDMRCores    = NumDMRGroups * 2;
  localparam int unsigned NumDMRLeftover = NumCores - NumDMRCores;

  localparam int unsigned CtrlConcatWidth = 1   + 1      + 5         + 1    + 32    + 1;
  //                                        busy  irq_ack  irq_ack_id  i_req  i_addr  d_req
  localparam int unsigned DataConcatWidth = 32      + 1       + DataWidth + BEWidth + UserWidth;
  //                                        data_add  data_wen  data_wdata  data_be   data_user
  localparam int unsigned MainConcatWidth = SeparateData ? CtrlConcatWidth : 
                                            CtrlConcatWidth + DataConcatWidth;

  logic [    NumCores-1:0][MainConcatWidth-1:0] main_concat_in;
  logic [NumTMRGroups-1:0][MainConcatWidth-1:0] main_tmr_out;
  logic [NumDMRGroups-1:0][MainConcatWidth-1:0] main_dmr_out;

  logic [    NumCores-1:0][DataConcatWidth-1:0] data_concat_in;
  logic [NumTMRGroups-1:0][DataConcatWidth-1:0] data_tmr_out;
  logic [NumDMRGroups-1:0][DataConcatWidth-1:0] data_dmr_out;

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

  // TODO: management unit

  if (TMRSupported || TMRFixed) begin
    /****************
     *  TMR Voters  *
     ****************/
    for (genvar i = 0; i < NumTMRGroups; i++) begin : gen_tmr_voters
      bitwise_TMR_voter #(
        .DataWidth( MainConcatWidth ),
        .VoterType( 0 )
      ) i_main_voter (
        .a_i        ( main_concat_in[i*3  ] ),
        .b_i        ( main_concat_in[i*3+1] ),
        .c_i        ( main_concat_in[i*3+2] ),
        .majority_o ( main_tmr_out  [i    ] ),
        .error_o    (),
        .error_cba_o()
      );
      if (SeparateData) begin : gen_data_voter
        bitwise_TMR_voter #(
          .DataWidth( DataConcatWidth ),
          .VoterType( 0 )
        ) i_main_voter (
          .a_i        ( data_concat_in[i*3  ] ),
          .b_i        ( data_concat_in[i*3+1] ),
          .c_i        ( data_concat_in[i*3+2] ),
          .majority_o ( data_tmr_out  [i    ] ),
          .error_o    (),
          .error_cba_o()
        );

        assign {tmr_core_busy_out[i], tmr_irq_ack_out[i], tmr_irq_ack_id_out[i],
               tmr_instr_req_out[i], tmr_instr_addr_out[i], tmr_data_req_out[i]} = main_tmr_out[i];
        assign {tmr_data_add_out[i], tmr_data_wen_out[i], tmr_data_wdata_out[i],
               tmr_data_be_out[i], tmr_data_user_out[i]} = data_tmr_out[i];
      end else begin : gen_out_assign
        assign {tmr_core_busy_out[i], tmr_irq_ack_out[i], tmr_irq_ack_id_out[i],
               tmr_instr_req_out[i], tmr_instr_addr_out[i], tmr_data_req_out[i],
               tmr_data_add_out[i], tmr_data_wen_out[i], tmr_data_wdata_out[i],
               tmr_data_be_out[i], tmr_data_user_out[i]} = main_tmr_out[i];
      end
    end
  end

  // Assign output signals
  if (DMRSupported && TMRSupported) begin : gen_full_HMR
    if (TMRFixed || DMRFixed) $fatal(1, "Cannot support both TMR and DMR and fix one!");

    // TODO

  end else if (TMRSupported || TMRFixed) begin : gen_TMR_only

    // TODO

  end else if (DMRSupported || DMRFixed) begin : gen_DMR_only

    // TODO

  end else begin : gen_no_redundancy
    // Direct assignment, disable all
    assign core_setback_o       = '0;
    
    assign core_core_id_o       = sys_core_id_i;
    assign core_cluster_id_o    = sys_cluster_id_i;

    assign core_clock_en_o      = sys_clock_en_i;
    assign core_fetch_en_o      = sys_fetch_en_i;
    assign core_boot_addr_o     = sys_boot_addr_i;
    assign sys_core_busy_o      = core_core_busy_i;

    assign core_irq_req_o       = sys_irq_req_i;
    assign sys_irq_ack_o        = core_irq_ack_i;
    assign core_irq_id_o        = sys_irq_id_i;
    assign sys_irq_ack_id_o     = core_irq_ack_id_i;

    assign sys_instr_req_o      = core_instr_req_i;
    assign core_instr_gnt_o     = sys_instr_gnt_i;
    assign sys_instr_addr_o     = core_instr_addr_i;
    assign core_instr_r_rdata_o = sys_instr_r_rdata_i;
    assign core_instr_r_valid_o = sys_instr_r_valid_i;
    assign core_instr_err_o     = sys_instr_err_i;

    assign core_debug_req_o     = sys_debug_req_i;

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

    assign core_perf_counters_o = sys_perf_counters_i;
  end

endmodule
