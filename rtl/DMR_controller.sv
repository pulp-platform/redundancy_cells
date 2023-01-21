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
  input  logic [NumDMRGroups-1:0] dmr_rf_checker_error_port_a_i,
  input  logic [NumDMRGroups-1:0] dmr_rf_checker_error_port_b_i,
  input  logic [NumDMRGroups-1:0] dmr_core_checker_error_main_i,
  input  logic [NumDMRGroups-1:0] dmr_core_checker_error_data_i,
  input  regfile_write_t [NumDMRGroups-1:0] recovery_regfile_write_i,
  output logic           [NumDMRGroups-1:0] regfile_readback_o,
  output regfile_raddr_t [NumDMRGroups-1:0] regfile_raddr_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_rstn_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_debug_req_o,
  input  logic           [NumDMRGroups-1:0] dmr_ctrl_core_debug_rsp_i,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_instr_lock_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_recover_o,
  output logic           [NumDMRGroups-1:0] dmr_ctrl_core_clk_en_o
);

/********************************************************
******************** Recovery Routine *******************
*********************************************************/
logic clear,
      routine_start;
logic core_instr_lock_rst,
      core_recover_rst;
logic addr_gen_start,
      addr_gen_error,
      addr_gen_done;

logic [RFAddrWidth-1:0] addr_gen_res;

logic [NumDMRGroups-1:0] dmr_ctrl_core_rstn_out     ,
                         dmr_ctrl_core_debug_rsp_in ,
                         dmr_ctrl_core_clk_en_out,
                         dmr_ctrl_core_debug_req_out,
                         dmr_ctrl_core_recover_d,
                         dmr_ctrl_core_recover_q,
                         dmr_ctrl_core_instr_lock_d,
                         dmr_ctrl_core_instr_lock_q;

recovery_routine_state_e current, next;
logic [$clog2(NumDMRGroups)-1:0] error_index_d,
                                 error_index_q;

for (genvar i = 0; i < NumDMRGroups; i++) begin
  assign dmr_ctrl_core_rstn_o [i] = dmr_ctrl_core_rstn_out [i];
  assign dmr_ctrl_core_clk_en_o [i] = dmr_ctrl_core_clk_en_out [i];
  assign dmr_ctrl_core_instr_lock_o [i] = ~dmr_ctrl_core_instr_lock_q [i];
  assign dmr_ctrl_core_debug_req_o [i] = dmr_ctrl_core_debug_req_out [i];
  assign dmr_ctrl_core_recover_o [i] = dmr_ctrl_core_recover_q [i];
  assign dmr_ctrl_core_debug_rsp_in [i] = dmr_ctrl_core_debug_rsp_i [i];
  assign regfile_readback_o [i] = '0;
  assign regfile_raddr_o [i] = '0;
end

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

assign routine_start = (|dmr_rf_checker_error_port_a_i) | 
                       (|dmr_rf_checker_error_port_a_i) |
                       (|dmr_core_checker_error_main_i) |
                       (|dmr_core_checker_error_data_i) ;
/************
* Registers *
*************/
/* 
 * Error index register. If the controller receives an error from one of the input NumDMRGroups,
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
 * Instruction lock registers. These registers prevent PULP obi adapter to propagate     
 * inexistent instruction requests towards iCache while the cores are in debug mode (halted) 
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
 * Core Recover Registers. These registers raise the recover signal towards the cores to     
 * allow their register files to be reloaded with the RRF content
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
  core_instr_lock_rst = 1'b0;
  dmr_ctrl_core_rstn_out = '1;
  dmr_ctrl_core_clk_en_out = '1;
  dmr_ctrl_core_recover_d = dmr_ctrl_core_recover_q;
  dmr_ctrl_core_instr_lock_d = dmr_ctrl_core_instr_lock_q;
  dmr_ctrl_core_debug_req_out = '0;
  case (current)
    IDLE: begin
      if (routine_start) begin
        next = RESET;
      end else
        next = current;
    end
    
    RESET: begin
      dmr_ctrl_core_rstn_out [error_index_q] = 1'b0;
      dmr_ctrl_core_instr_lock_d [error_index_q] = 1'b1;
      next = HALT_REQ;
    end
    
    HALT_REQ: begin
      dmr_ctrl_core_debug_req_out [error_index_q] = 1'b1;
      next = HALT_WAIT;
    end

    HALT_WAIT: begin
      if ( dmr_ctrl_core_debug_rsp_in [error_index_q] ) begin
        next = RESTORE_RF;
      end else
        next = current;      
    end
    
    RESTORE_PC: begin
    
    end
    
    RESTORE_RF: begin
      dmr_ctrl_core_recover_d [error_index_q] = 1'b1;
      addr_gen_start = 1'b1;
      if (addr_gen_done)
        next = RESTORE_CSR;
      else
      next = current;
    end
    
    RESTORE_CSR: begin
    end
  endcase
end : recovery_routine_fsm

/***************************************************
******************** RF Readback *******************
****************************************************/

/* Come back here later*/

// logic [NumDMRGroups-1:0] core_clk_int,
//                          core_clk_pre,
//                          regfile_error_a,
//                          regfile_error_b;
// logic [NumDMRGroups-1:0] core_rst;
// logic [RegfileAddr-1:0] regfile_read_a,
//                         regfile_read_b;
// 
// always_ff @(posedge clk_i, negedge rst_ni) begin
//   if (~rst_ni)
//     core_clk_pre <= 1'b1;
//   else if (|core_clk_int)
//     core_clk_pre <= 1'b0;
// end
// 
// always_ff @(posedge clk_i, negedge rst_ni) begin
//   if (~rst_ni) begin
//     core_clk_o <= 1'b1;
//     regfile_readback_o <= '0;
//   end else /*if (|core_clk_int)*/ begin
//     core_clk_o <= core_clk_pre;
//     for (int i = 0; i < NumDMRGroups; i++)
//       regfile_readback_o[i] <= (dmr_rf_checker_error_port_a_i[i] || 
//                                 dmr_rf_checker_error_port_b_i[i] ) ? 1'b1 : 1'b0;
//   end
// end
// 
// always_ff @(posedge clk_i, negedge rst_ni) begin
//   if (~rst_ni) begin
//     regfile_raddr_o <= '0;
//   end else begin
//     for (int i = 0; i < NumDMRGroups; i++) begin
//       if (dmr_rf_checker_error_port_a_i[i])
//         regfile_raddr_o[i].raddr_a <= recovery_regfile_write_i[i].waddr_a;
//       else if (dmr_rf_checker_error_port_b_i[i])
//         regfile_raddr_o[i].raddr_b <= recovery_regfile_write_i[i].waddr_b;
//       else begin
//         regfile_raddr_o[i].raddr_a <= '0;
//         regfile_raddr_o[i].raddr_b <= '0;
//       end
//     end
//   end
// end

// assign regfile_read_a = |regfile_error_a;
// assign regfile_read_b = |regfile_error_b;
// 
// for (genvar i = 0; i < NumDMRGroups; i++) begin
//   assign core_clk_int [i] = (dmr_rf_checker_error_port_a_i[i] || 
//                              dmr_rf_checker_error_port_b_i[i] ) ? 1'b1 : 1'b0;
// 
//   assign regfile_error_a [i] = dmr_rf_checker_error_port_a_i [i] ? 1'b0 : 1'b1;
//   assign regfile_error_b [i] = dmr_rf_checker_error_port_b_i [i] ? 1'b0 : 1'b1;
//   
//   assign regfile_readback_o [i] = (dmr_rf_checker_error_port_a_i[i] || 
//                                    dmr_rf_checker_error_port_b_i[i] ) ? 1'b1 : 1'b0;
// 
//   assign regfile_raddr_o[i].raddr_a = (dmr_rf_checker_error_port_a_i[i]) ? 
//                                       recovery_regfile_write_i[i].waddr_a : '0;
// 
//   assign regfile_raddr_o[i].raddr_b = (dmr_rf_checker_error_port_b_i[i]) ? 
//                                       recovery_regfile_write_i[i].waddr_b : '0;
// end

endmodule : DMR_controller
