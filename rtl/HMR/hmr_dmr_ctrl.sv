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

module hmr_dmr_ctrl
  import rapid_recovery_pkg::*;
#(
  parameter bit  InterleaveGrps = 1'b0,
  parameter int  unsigned DataWidth = 32,
  parameter bit  DMRFixed       = 1'b0,
  parameter bit  DefaultInDMR   = DMRFixed ? 1'b1 : 1'b0,
  parameter bit  RapidRecovery  = 1'b0,
  parameter type apb_req_t      = logic,
  parameter type apb_resp_t     = logic
) (
  input  logic       clk_i,
  input  logic       rst_ni,
  // input  logic       test_enable_i,

  // Register interface
  input  apb_req_t   reg_req_i,
  output apb_resp_t  reg_resp_o,

  // CTRL from external (e.g. HMR ctrl regs)
  input  logic       dmr_enable_q_i,
  input  logic       dmr_enable_qe_i,
  input  logic       rapid_recovery_q_i,
  input  logic       rapid_recovery_qe_i,
  input  logic       force_recovery_q_i,
  input  logic       force_recovery_qe_i,

  // DMR control signals
  output logic [1:0] setback_o,
  output logic       sw_resynch_req_o,
  output logic       sw_synch_req_o,
  output logic [DataWidth-1:0] checkpoint_o,
  output logic       grp_in_independent_o,
  output logic       rapid_recovery_en_o,
  output logic [1:0] dmr_incr_mismatches_o,
  input  logic       dmr_error_i,
  output logic       recovery_request_o,
  input  logic       recovery_finished_i,

  input  logic       fetch_en_i,
  input  logic       cores_synch_i
);

  logic synch_req,   synch_req_sent_d,   synch_req_sent_q;
  logic resynch_req, resynch_req_sent_d, resynch_req_sent_q;
  logic cores_synch_q;

  typedef enum logic [2:0] {NON_DMR, DMR_RUN, DMR_RESTORE} dmr_mode_e;
  localparam dmr_mode_e DefaultDMRMode = DefaultInDMR || DMRFixed ? DMR_RUN : NON_DMR;

  hmr_dmr_regs_reg_pkg::hmr_dmr__out_t dmr_reg2hw;
  hmr_dmr_regs_reg_pkg::hmr_dmr__in_t dmr_hw2reg;

  dmr_mode_e dmr_red_mode_d, dmr_red_mode_q;

  assign grp_in_independent_o = dmr_red_mode_q == NON_DMR;
  assign rapid_recovery_en_o = dmr_reg2hw.dmr_config.rapid_recovery.value && RapidRecovery;

  assign sw_synch_req_o = synch_req & ~synch_req_sent_q;
  assign synch_req_sent_d = synch_req;
  assign sw_resynch_req_o = resynch_req & ~resynch_req_sent_q;
  assign resynch_req_sent_d = resynch_req;
  assign checkpoint_o = dmr_reg2hw.checkpoint_addr.checkpoint_addr.value;

  hmr_dmr_regs_reg_top i_dmr_regs (
    .clk(clk_i),
    .arst_n(rst_ni),
    .s_apb_psel(reg_req_i.psel),
    .s_apb_penable(apb_req_i.penable),
    .s_apb_pwrite(apb_req_i.pwrite),
    .s_apb_pprot(apb_req_i.pprot),
    .s_apb_paddr(apb_req_i.paddr[3:0]),
    .s_apb_pwdata(apb_req_i.pwdata),
    .s_apb_pstrb(apb_req_i.pstrb),
    .s_apb_pready(apb_resp_o.pready),
    .s_apb_prdata(apb_resp_o.prdata),
    .s_apb_pslverr(apb_resp_o.pslverr),
    .hwif_in(dmr_hw2reg),
    .hwif_out(dmr_reg2hw)
  );

  // Global config update
  assign dmr_hw2reg.dmr_enable.dmr_enable.we       = dmr_enable_qe_i;
  assign dmr_hw2reg.dmr_enable.dmr_enable.next     = dmr_enable_q_i;
  assign dmr_hw2reg.dmr_config.rapid_recovery.we   = rapid_recovery_qe_i || ~RapidRecovery;
  assign dmr_hw2reg.dmr_config.rapid_recovery.next = rapid_recovery_q_i && RapidRecovery;
  assign dmr_hw2reg.dmr_config.force_recovery.next = force_recovery_qe_i ? force_recovery_q_i : 1'b0;

  /**************************
   *  FSM for DMR lockstep  *
   **************************/

  always_comb begin : proc_fsm
    setback_o = 2'b00;
    dmr_red_mode_d = dmr_red_mode_q;
    dmr_incr_mismatches_o = '0;
    recovery_request_o = 1'b0;
    resynch_req = 1'b0;
    synch_req = 1'b0;

    dmr_hw2reg.dmr_config.force_recovery.we = force_recovery_qe_i;

    case (dmr_red_mode_q)
      DMR_RUN: begin
        // If forced execute recovery
        if (dmr_reg2hw.dmr_config.force_recovery.value && RapidRecovery &&
            dmr_reg2hw.dmr_config.rapid_recovery.value) begin
          dmr_hw2reg.dmr_config.force_recovery.we = 1'b1;
          dmr_red_mode_d = DMR_RESTORE;
        end

        // If error detected, restore
        if (dmr_error_i && RapidRecovery && dmr_reg2hw.dmr_config.rapid_recovery.value) begin
          $display("[HMR-dual] %t - mismatch detected, rapid recovery starting", $realtime);
          dmr_red_mode_d = DMR_RESTORE;
        end

        if (dmr_error_i && (!RapidRecovery || !dmr_reg2hw.dmr_config.rapid_recovery.value)) begin
          $display("[HMR-dual] %t - mismatch detected, SW trigger", $realtime);
          resynch_req = 1'b1;
        end
      end

      DMR_RESTORE: begin
        recovery_request_o = 1'b1;
        if (recovery_finished_i) begin
          $display("[HMR-dual] %t - mismatch restored", $realtime);
          dmr_red_mode_d = DMR_RUN;
        end
      end

      // Default: do nothing
      default: ;
    endcase

    // Logic to switch in and out of DMR
    if (!DMRFixed) begin
      // Set DMR mode on external signal that cores are synchronized
      if (dmr_red_mode_q == NON_DMR && dmr_reg2hw.dmr_enable.dmr_enable.value == 1'b1) begin
        synch_req = 1'b1;
        if (cores_synch_q == 1'b1) begin
          if (dmr_reg2hw.dmr_config.rapid_recovery.value == 1'b1) begin
            dmr_red_mode_d = DMR_RESTORE;
          end else begin
            dmr_red_mode_d = DMR_RUN;
            setback_o = 2'b11;
          end
        end
      end
      // Before core startup: set DMR mode from reg2hw.dmr_enable
      if (fetch_en_i == 0) begin
        if (dmr_reg2hw.dmr_enable.dmr_enable.value == 1'b0) begin
          dmr_red_mode_d = NON_DMR;
        end else begin
          synch_req = 1'b0;
          dmr_red_mode_d = DMR_RUN;
        end
      end
      // split tolerant mode to performance mode anytime (but require correct core state)
      if (dmr_red_mode_q == DMR_RUN) begin
        if (dmr_reg2hw.dmr_enable.dmr_enable.value == 1'b0) begin
          dmr_red_mode_d = NON_DMR;
          setback_o = 2'b10;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_red_mode
    if(!rst_ni) begin
      dmr_red_mode_q <= DefaultDMRMode;
      synch_req_sent_q <= '0;
      resynch_req_sent_q <= '0;
      cores_synch_q <= '0;
    end else begin
      dmr_red_mode_q <= dmr_red_mode_d;
      synch_req_sent_q <= synch_req_sent_d;
      resynch_req_sent_q <= resynch_req_sent_d;
      cores_synch_q <= cores_synch_i;
    end
  end

endmodule
