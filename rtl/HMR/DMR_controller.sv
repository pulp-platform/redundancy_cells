/* Copyright 2020 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 * 
 * Dual Modular Redundancy Controller
 * Handles the occurrence of errors and starts recovery routine 
 * 
 */

import recovery_pkg::*;

module DMR_controller #(
  parameter  int unsigned NumCores       = 0,
  parameter  bit          DMRFixed       = 1'b0,
  parameter  int unsigned RFAddrWidth    = 6,
  localparam int unsigned NumDMRGroups   = NumCores/2,
  localparam int unsigned NumDMRCores    = NumDMRGroups * 2,
  localparam int unsigned NumDMRLeftover = NumCores - NumDMRCores,
  localparam int unsigned NumSysCores    = DMRFixed ? NumDMRCores : NumCores
)(
  input  logic clk_i ,
  input  logic rst_ni,
  output logic intruder_lock_o,
  input  logic [NumDMRGroups-1:0] dmr_rf_checker_error_port_a_i,
  input  logic [NumDMRGroups-1:0] dmr_rf_checker_error_port_b_i,
  input  logic [NumDMRGroups-1:0] dmr_core_checker_error_main_i,
  input  logic [NumDMRGroups-1:0] dmr_core_checker_error_data_i,
  input  regfile_write_t [NumDMRGroups-1:0] backup_regfile_write_i,
  output regfile_write_t [NumDMRGroups-1:0] core_recovery_regfile_wport_o,
  output logic           [NumDMRGroups-1:0] regfile_readback_o,
  output regfile_raddr_t [NumDMRGroups-1:0] regfile_raddr_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_pc_read_enable_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_pc_write_enable_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_debug_req_o,
  input  logic           [NumDMRGroups-1:0] dmr_ctrl_core_debug_rsp_i,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_instr_lock_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_setback_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_recover_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_debug_resume_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_clk_en_o
);

/********************************************************
******************** Recovery Routine *******************
*********************************************************/
/************************
 * Signals Declarations *
 ************************/
logic clear,
      routine_start;
logic core_instr_lock_rst,
      core_recover_rst,
      pc_write_enable_rst;
logic addr_gen_start,
      addr_gen_error,
      addr_gen_done;

logic intruder_lock_d,
      intruder_lock_q;

logic restore_pc_cycles_d,
      restore_pc_cycles_q,
      restore_pc_cycles_rst;

logic [RFAddrWidth-1:0] addr_gen_res;

logic [NumDMRGroups-1:0] dmr_ctrl_core_setback_out  ,
                         dmr_ctrl_core_debug_rsp_in ,
                         dmr_ctrl_core_clk_en_out,
                         dmr_ctrl_core_debug_req_out,
                         dmr_ctrl_pc_read_enable_out,
                         dmr_ctrl_pc_write_enable_d,
                         dmr_ctrl_pc_write_enable_q,
                         dmr_ctrl_core_recover_d,
                         dmr_ctrl_core_recover_q,
                         dmr_ctrl_core_instr_lock_d,
                         dmr_ctrl_core_instr_lock_q;

recovery_routine_state_e current, next;
logic [$clog2(NumDMRGroups)-1:0] error_index_d,
                                 error_index_q;
/******************
 * Output Assigns *
 ******************/
for (genvar i = 0; i < NumDMRGroups; i++) begin
  assign dmr_ctrl_core_setback_o [i] = dmr_ctrl_core_setback_out [i];
  assign dmr_ctrl_core_clk_en_o [i] = dmr_ctrl_core_clk_en_out [i];
  assign dmr_ctrl_pc_read_enable_o [i] = dmr_ctrl_pc_read_enable_out [i];
  assign dmr_ctrl_pc_write_enable_o [i] = dmr_ctrl_pc_write_enable_q [i];
  assign dmr_ctrl_core_instr_lock_o [i] = dmr_ctrl_core_instr_lock_q [i];
  assign dmr_ctrl_core_debug_req_o [i] = dmr_ctrl_core_debug_req_out [i];
  assign dmr_ctrl_core_recover_o [i] = dmr_ctrl_core_recover_q [i];
  assign dmr_ctrl_core_debug_rsp_in [i] = dmr_ctrl_core_debug_rsp_i [i];
  assign regfile_readback_o [i] = '0;
  assign regfile_raddr_o [i] = '0;
end
assign intruder_lock_o = intruder_lock_q;

/**************
 * Comb logic *
 **************/

/*
 * Error index identifier.
 * Identifies the index of the group that is faulty.
 */
always_comb begin
  error_index_d = error_index_q;
  for (int i = 0; i < NumDMRGroups; i++) begin
    if (dmr_rf_checker_error_port_a_i [i] ||
        dmr_rf_checker_error_port_b_i [i] ||
        dmr_core_checker_error_main_i [i] ||
        dmr_core_checker_error_data_i [i]  )
      error_index_d = i;
  end
end

/*
 * Routine start signal.
 * Checks if there are any errors from external checkers to start the FSM Recovery Routine.
 */
assign routine_start = (|dmr_rf_checker_error_port_a_i) | 
                       (|dmr_rf_checker_error_port_a_i) |
                       (|dmr_core_checker_error_main_i) |
                       (|dmr_core_checker_error_data_i) ;
/************
* Registers *
*************/

/*
 * Intruder lock signal.
 * At the end of the recovery routine, we lock the intruder a prevent it
 * to continuously inject undesired faults.
 */
always_ff @(posedge clk_i, negedge rst_ni) begin : intruder_lock
  if (~rst_ni)
    intruder_lock_q <= 1'b0;
  else begin
    intruder_lock_q <= intruder_lock_d;
  end
end

/*
 * Error index register.
 * If the controller receives an error from one of the input NumDMRGroups,
 * this register saves the index of the faulty input group.
 */
always_ff @(posedge clk_i, negedge rst_ni) begin : error_index_register
  if (~rst_ni)
    error_index_q <= '0;
  else begin
    if (clear)
      error_index_q <= '0;
    else
      error_index_q <= error_index_d;
  end
end

/*
 * Instruction lock registers.
 * These registers prevent PULP obi adapter to propagate
 * inexistent instruction requests towards iCache while the cores are in debug mode (halted).
 */
generate
  for (genvar i = 0; i < NumDMRGroups; i++) begin
    always_ff @(posedge clk_i, negedge rst_ni) begin : instruction_lock_registers
      if (~rst_ni) begin
        dmr_ctrl_core_instr_lock_q [i] <= 1'b0;
      end else begin
        if (clear || core_instr_lock_rst) begin
          dmr_ctrl_core_instr_lock_q [i] <= 1'b0;
        end else
          dmr_ctrl_core_instr_lock_q [i] <= dmr_ctrl_core_instr_lock_d [i];
      end
    end
  end
endgenerate

/*
 * Core Recover Registers.
 * These registers raise the recover signal towards the cores to
 * allow their register files to be reloaded with the RRF content.
 */
generate
  for (genvar i = 0; i < NumDMRGroups; i++) begin
    always_ff @(posedge clk_i, negedge rst_ni) begin : core_recover_registers
      if (~rst_ni) begin
        dmr_ctrl_core_recover_q [i] <= 1'b0;
      end else begin
        if (clear || core_recover_rst) begin
          dmr_ctrl_core_recover_q [i] <= 1'b0;
        end else
          dmr_ctrl_core_recover_q [i] <= dmr_ctrl_core_recover_d [i];
      end
    end
  end
endgenerate

/*
 * Program Counter Write Enable Register.
 * During a recovery routine, this register blocks the Recovery PC
 * from sampling new values from the cores.
 */
generate
  for (genvar i = 0; i < NumDMRGroups; i++) begin
    always_ff @(posedge clk_i, negedge rst_ni) begin : program_counter_write_enable
      if (~rst_ni) begin
        dmr_ctrl_pc_write_enable_q [i] <= 1'b1;
      end else begin
        if (clear || pc_write_enable_rst) begin
          dmr_ctrl_pc_write_enable_q [i] <= 1'b1;
        end else
          dmr_ctrl_pc_write_enable_q [i] <= dmr_ctrl_pc_write_enable_d [i];
      end
    end
  end
endgenerate

/*
 * Program Counter Restore Counter.
 * Counter that keeps the Recovery Routine FSM in the RECOVERY_PC state
 * for two cycles to make sure that the PC state is safely restored.
 */
always_ff @(posedge clk_i, negedge rst_ni) begin : pc_restore_counter
  if (~rst_ni)
    restore_pc_cycles_q <= '0;
  else begin
    if (clear || restore_pc_cycles_rst)
      restore_pc_cycles_q <= '0;
    else
      restore_pc_cycles_q <= restore_pc_cycles_d;
  end
end

/***********************
* RF Address Generator *
************************/
DMR_address_generator #(
  .AddrWidth ( RFAddrWidth )
) RF_address_generator (
  .clk_i     ( clk_i          ),
  .rst_ni    ( rst_ni         ),
  .clear_i   ( clear          ),
  .enable_i  ( addr_gen_start ),
  .done_o    ( addr_gen_done  ),
  .fatal_o   ( addr_gen_error ),
  .address_o ( addr_gen_res   )
);

/* Binding recovery signals towards RRF and cores */
always_comb begin : RF_ports_binding
  core_recovery_regfile_wport_o = '0;
  for (int i = 0; i < NumDMRGroups; i++) begin
    if (i == error_index_q) begin
      core_recovery_regfile_wport_o[i].we_a = (addr_gen_start) ? 1'b1 : 1'b0;
      core_recovery_regfile_wport_o[i].waddr_a = addr_gen_res;
      core_recovery_regfile_wport_o[i].we_b = (addr_gen_start) ? 1'b1 : 1'b0;
      core_recovery_regfile_wport_o[i].waddr_b = 5'd16 + addr_gen_res;
    end else
      core_recovery_regfile_wport_o = '0;
  end
end

/********************************
* Recovery Routine State Update *
*********************************/
always_ff @(posedge clk_i, negedge rst_ni) begin : recovery_routine_register
  if (~rst_ni)
    current <= IDLE;
  else begin
    current <= next;
  end
end

/***********************
* Recovery Routine FSM *
************************/
always_comb begin : recovery_routine_fsm
  next = current;
  clear = 1'b0;
  addr_gen_start = 1'b0;
  core_recover_rst = '0;
  pc_write_enable_rst = 1'b0;
  core_instr_lock_rst = 1'b0;
  restore_pc_cycles_rst = 1'b0;
  dmr_ctrl_core_setback_out = '0;
  dmr_ctrl_core_clk_en_out = '1;
  dmr_ctrl_core_recover_d = dmr_ctrl_core_recover_q;
  dmr_ctrl_core_instr_lock_d = dmr_ctrl_core_instr_lock_q;
  dmr_ctrl_core_debug_req_out = '0;
  dmr_ctrl_core_debug_resume_o = '0;
  dmr_ctrl_pc_read_enable_out = '0;
  dmr_ctrl_pc_write_enable_d = dmr_ctrl_pc_write_enable_q;
  intruder_lock_d = intruder_lock_q;
  restore_pc_cycles_d = restore_pc_cycles_q;
  case (current)
    IDLE: begin
      if (routine_start) begin
        next = RESET;
      end else
        next = current;
    end
    
    RESET: begin
      dmr_ctrl_core_setback_out [error_index_q] = 1'b1;
      dmr_ctrl_core_instr_lock_d [error_index_q] = 1'b1;
      dmr_ctrl_pc_write_enable_d [error_index_q] = 1'b0;
      next = HALT_REQ;
    end
    
    HALT_REQ: begin
      dmr_ctrl_core_debug_req_out [error_index_q] = 1'b1;
      next = HALT_WAIT;
    end

    HALT_WAIT: begin
      if (dmr_ctrl_core_debug_rsp_in [error_index_q]) begin
        next = RESTORE_PC;
      end else
        next = current;
    end

    RESTORE_PC: begin
      dmr_ctrl_pc_read_enable_out [error_index_q] = 1'b1;
      restore_pc_cycles_d = restore_pc_cycles_q + 1'd1;
      if (restore_pc_cycles_q == 1'd1) begin
        restore_pc_cycles_d = 1'd0;
        next = RESTORE_RF;
      end else
        next = current;
    end
    
    RESTORE_RF: begin
      dmr_ctrl_core_recover_d [error_index_q] = 1'b1;
      addr_gen_start = 1'b1;
      if (addr_gen_done) begin
        dmr_ctrl_core_instr_lock_d [error_index_q] = 1'b0;
        dmr_ctrl_core_debug_resume_o [error_index_q] = 1'b1;
        next = EXIT;
      end else
        next = current;
    end
    
    RESTORE_CSR: begin
    end

    EXIT: begin
      clear = 1'b1;
      intruder_lock_d = 1'b1;
      next =  IDLE;
    end
  endcase
end : recovery_routine_fsm

endmodule : DMR_controller
