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
// Hybrid modular redundancy TMR control unit

module hmr_tmr_ctrl #(
  parameter bit  InterleaveGrps = 1'b0,
  parameter bit  TMRFixed       = 1'b0,
  parameter bit  DefaultInTMR   = TMRFixed ? 1'b1 : 1'b0,
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
  input  logic       tmr_enable_q_i,
  input  logic       tmr_enable_qe_i,
  input  logic       delay_resynch_q_i,
  input  logic       delay_resynch_qe_i,
  input  logic       setback_q_i,
  input  logic       setback_qe_i,
  input  logic       reload_setback_q_i,
  input  logic       reload_setback_qe_i,
  input  logic       force_resynch_q_i,
  input  logic       force_resynch_qe_i,
  
  // TMR control signals
  output logic       setback_o,
  output logic       sw_resynch_req_o,
  output logic       grp_in_independent_o,
  output logic [2:0] tmr_incr_mismatches_o,
  input  logic       tmr_single_mismatch_i,
  input  logic [2:0] tmr_error_i,
  input  logic       tmr_failure_i,
  input  logic       fetch_en_i,
  input  logic       cores_synch_i
);

  typedef enum logic [1:0] {NON_TMR, TMR_RUN, TMR_UNLOAD, TMR_RELOAD} tmr_mode_e;
  localparam tmr_mode_e DefaultTMRMode = DefaultInTMR || TMRFixed ? TMR_RUN : NON_TMR;

  hmr_tmr_regs_reg_pkg::hmr_tmr_regs_reg2hw_t tmr_reg2hw;
  hmr_tmr_regs_reg_pkg::hmr_tmr_regs_hw2reg_t tmr_hw2reg;

  tmr_mode_e tmr_red_mode_d, tmr_red_mode_q;
  logic tmr_setback_d, tmr_setback_q;

  assign setback_o = tmr_setback_q;
  assign grp_in_independent_o = tmr_red_mode_q == NON_TMR;
  assign tmr_resynch_req_o = tmr_red_mode_q == TMR_UNLOAD;

  hmr_tmr_regs_reg_top #(
    .reg_req_t(reg_req_t),
    .reg_rsp_t(reg_resp_t)
  ) i_tmr_regs (
    .clk_i,
    .rst_ni,
    .reg_req_i(reg_req_i),
    .reg_rsp_o(reg_resp_o),
    .reg2hw   (tmr_reg2hw),
    .hw2reg   (tmr_hw2reg),
    .devmode_i('0)
  );

  // Global config update
  assign tmr_hw2reg.tmr_enable.de = tmr_enable_qe_i;
  assign tmr_hw2reg.tmr_enable.d  = tmr_enable_q_i;
  assign tmr_hw2reg.tmr_config.delay_resynch.de  = delay_resynch_qe_i;
  assign tmr_hw2reg.tmr_config.delay_resynch.d   = delay_resynch_q_i;
  assign tmr_hw2reg.tmr_config.setback.de        = setback_qe_i;
  assign tmr_hw2reg.tmr_config.setback.d         = setback_q_i;
  assign tmr_hw2reg.tmr_config.reload_setback.de = reload_setback_qe_i;
  assign tmr_hw2reg.tmr_config.reload_setback.d  = reload_setback_q_i;
  assign tmr_hw2reg.tmr_config.force_resynch.d   = force_resynch_qe_i ? force_resynch_q_i : 1'b0;

  /**************************
   *  FSM for TMR lockstep  *
   **************************/
  always_comb begin : proc_fsm
    tmr_setback_d = 1'b0;
    tmr_red_mode_d = tmr_red_mode_q;
    tmr_incr_mismatches_o = '0;

    tmr_hw2reg.tmr_config.force_resynch.de  = force_resynch_qe_i;

    case (tmr_red_mode_q)
      TMR_RUN: begin
        // If forced execute resynchronization
        if (tmr_reg2hw.tmr_config.force_resynch.q) begin
          tmr_hw2reg.tmr_config.force_resynch.de = 1'b1;
          if (tmr_reg2hw.tmr_config.delay_resynch == 0) begin
            tmr_red_mode_d = TMR_UNLOAD;
            // TODO: buffer the restoration until delay_resynch is disabled
          end
        end

        // If error detected, do resynchronization
        if (tmr_single_mismatch_i) begin
          $display("[ODRG] %t - mismatch detected", $realtime);
          if (tmr_error_i[0]) tmr_incr_mismatches_o[0] = 1'b1;
          if (tmr_error_i[1]) tmr_incr_mismatches_o[1] = 1'b1;
          if (tmr_error_i[2]) tmr_incr_mismatches_o[2] = 1'b1;

          if (tmr_reg2hw.tmr_config.delay_resynch == 0) begin
            tmr_red_mode_d = TMR_UNLOAD;
            // TODO: buffer the restoration until delay_resynch is disabled
          end
        end
      end

      TMR_UNLOAD: begin
        // If unload complete, go to reload (and reset)
        if (tmr_reg2hw.sp_store.q != '0) begin
          tmr_red_mode_d = TMR_RELOAD;
          if (tmr_reg2hw.tmr_config.setback.q) begin
            tmr_setback_d = 1'b1;
          end
        end
      end

      TMR_RELOAD: begin
        // If reload complete, finish (or reset if error happens during reload)
        if (tmr_reg2hw.sp_store.q == '0) begin
          $display("[ODRG] %t - mismatch restored", $realtime);
          tmr_red_mode_d = TMR_RUN;
        end else begin
          if ((tmr_single_mismatch_i || tmr_failure_i) && tmr_reg2hw.tmr_config.setback.q &&
              tmr_reg2hw.tmr_config.reload_setback.q &&
              !(tmr_reg2hw.sp_store.qe && reg_req_i.wdata == '0)) begin
            tmr_setback_d = 1'b1;
          end
        end
      end

      // Default: do nothing

    endcase

    // Logic to switch in and out of TMR
    if (!TMRFixed) begin
      // Before core startup: set TMR mode from reg2hw.tmr_enable
      if (fetch_en_i == 0) begin
        if (tmr_reg2hw.tmr_enable.q == 1'b0) begin
          tmr_red_mode_d = NON_TMR;
        end else begin
          tmr_red_mode_d = TMR_RUN;
        end
      end
      // split tolerant mode to performance mode anytime (but require correct core state)
      if (tmr_red_mode_q == TMR_RUN) begin
        if (tmr_reg2hw.tmr_enable.q == 1'b0) begin
          tmr_red_mode_d = NON_TMR;
        end
      end
      // Set TMR mode on external signal that cores are synchronized
      if (tmr_red_mode_q == NON_TMR && cores_synch_i) begin
        if (tmr_reg2hw.tmr_enable.q == 1'b1) begin
          tmr_red_mode_d = TMR_RUN;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_red_mode
    if(!rst_ni) begin
      tmr_red_mode_q <= DefaultTMRMode;
      tmr_setback_q <= '0;
    end else begin
      tmr_red_mode_q <= tmr_red_mode_d;
      tmr_setback_q <= tmr_setback_d;
    end
  end

endmodule
