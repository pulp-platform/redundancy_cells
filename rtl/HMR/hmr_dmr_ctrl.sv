// Copyright 2023 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Hybrid modular redundancy DMR control unit

module hmr_dmr_ctrl import recovery_pkg::*; #(
  parameter bit  InterleaveGrps = 1'b0,
  parameter bit  DMRFixed       = 1'b0,
  parameter bit  DefaultInDMR   = DMRFixed ? 1'b1 : 1'b0,
  parameter bit  RapidRecovery  = 1'b0,
  parameter type reg_req_t      = logic,
  parameter type reg_resp_t     = logic
) (
  input  logic       clk_i,
  input  logic       rst_ni,
  // input  logic       test_enable_i,

  // Register interface
  input  reg_req_t   reg_req_i,
  output reg_resp_t  reg_resp_o,

  // CTRL from external (e.g. HMR ctrl regs)
  input  logic       dmr_enable_q_i,
  input  logic       dmr_enable_qe_i,
  input  logic       rapid_recovery_q_i,
  input  logic       rapid_recovery_qe_i,
  input  logic       force_recovery_q_i,
  input  logic       force_recovery_qe_i,

  // DMR control signals
  output logic       setback_o,
  output logic       sw_resynch_req_o,
  output logic       grp_in_independent_o,
  output logic [1:0] dmr_incr_mismatches_o,
  input  logic       dmr_error_i,
  output logic       recovery_request_o,
  input  logic       recovery_finished_i,

  input  logic       fetch_en_i,
  input  logic       cores_synch_i
);

  typedef enum logic [2:0] {NON_DMR, DMR_RUN, DMR_RESTORE} dmr_mode_e;
  localparam dmr_mode_e DefaultDMRMode = DefaultInDMR || DMRFixed ? DMR_RUN : NON_DMR;

  hmr_dmr_regs_reg_pkg::hmr_dmr_regs_reg2hw_t dmr_reg2hw;
  hmr_dmr_regs_reg_pkg::hmr_dmr_regs_hw2reg_t dmr_hw2reg;

  dmr_mode_e dmr_red_mode_d, dmr_red_mode_q;
  logic dmr_setback_d, dmr_setback_q;

  assign setback_o = dmr_setback_q;
  assign grp_in_independent_o = dmr_red_mode_q == NON_DMR;

  hmr_dmr_regs_reg_top #(
    .reg_req_t(reg_req_t),
    .reg_rsp_t(reg_resp_t)
  ) i_tmr_regs (
    .clk_i,
    .rst_ni,
    .reg_req_i(reg_req_i),
    .reg_rsp_o(reg_resp_o),
    .reg2hw   (dmr_reg2hw),
    .hw2reg   (dmr_hw2reg),
    .devmode_i('0)
  );

  // Global config update
  assign dmr_hw2reg.dmr_enable.de = dmr_enable_qe_i;
  assign dmr_hw2reg.dmr_enable.d  = dmr_enable_q_i;
  assign dmr_hw2reg.dmr_config.rapid_recovery.de = rapid_recovery_qe_i;
  assign dmr_hw2reg.dmr_config.rapid_recovery.d  = rapid_recovery_q_i;
  assign dmr_hw2reg.dmr_config.force_recovery.d  = force_recovery_qe_i ? force_recovery_q_i : 1'b0;

  /**************************
   *  FSM for DMR lockstep  *
   **************************/

  always_comb begin : proc_fsm
    dmr_setback_d = 1'b0;
    dmr_red_mode_d = dmr_red_mode_q;
    dmr_incr_mismatches_o = '0;

    dmr_hw2reg.dmr_config.force_recovery.de = force_recovery_qe_i;

    case (dmr_red_mode_q)
      DMR_RUN: begin
        // If forced execute recovery
        if (dmr_reg2hw.dmr_config.force_recovery.q && RapidRecovery) begin
          dmr_hw2reg.dmr_config.force_recovery.de = 1'b1;
          dmr_red_mode_d = DMR_RESTORE;
        end

        // If error detected, restore
        if (dmr_error_i && RapidRecovery) begin
          dmr_red_mode_d = DMR_RESTORE;
          recovery_request_o = 1'b1;
        end
      end

      DMR_RESTORE: begin
        if (recovery_finished_i) begin
          dmr_red_mode_d = DMR_RUN;
        end
      end

      // Default: do nothing
    endcase

    // Logic to switch in and out of DMR
    if (!DMRFixed) begin
      // Before core startup: set DMR mode from reg2hw.dmr_enable
      if (fetch_en_i == 0) begin
        if (dmr_reg2hw.dmr_enable.q == 1'b0) begin
          dmr_red_mode_d = NON_DMR;
        end else begin
          dmr_red_mode_d = DMR_RUN;
        end
      end
      // split tolerant mode to performance mode anytime (but require correct core state)
      if (dmr_red_mode_q == DMR_RUN) begin
        if (dmr_reg2hw.dmr_enable.q == 1'b0) begin
          dmr_red_mode_d = NON_DMR;
        end
      end
      // Set DMR mode on external signal that cores are synchronized
      if (dmr_red_mode_q == NON_DMR && cores_synch_i) begin
        if (dmr_reg2hw.dmr_enable.q == 1'b1) begin
          dmr_red_mode_d = DMR_RUN;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_red_mode
    if(!rst_ni) begin
      dmr_red_mode_q <= DefaultDMRMode;
      dmr_setback_q <= '0;
    end else begin
      dmr_red_mode_q <= dmr_red_mode_d;
      dmr_setback_q <= dmr_setback_d;
    end
  end

endmodule
