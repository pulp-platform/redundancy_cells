// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Top module auto-generated by `reggen`


`include "common_cells/assertions.svh"

module hmr_core_regs_reg_top #(
  parameter type reg_req_t = logic,
  parameter type reg_rsp_t = logic,
  parameter int AW = 4
) (
  input logic clk_i,
  input logic rst_ni,
  input  reg_req_t reg_req_i,
  output reg_rsp_t reg_rsp_o,
  // To HW
  output hmr_core_regs_reg_pkg::hmr_core_regs_reg2hw_t reg2hw, // Write
  input  hmr_core_regs_reg_pkg::hmr_core_regs_hw2reg_t hw2reg, // Read


  // Config
  input devmode_i // If 1, explicit error return for unmapped register access
);

  import hmr_core_regs_reg_pkg::* ;

  localparam int DW = 32;
  localparam int DBW = DW/8;                    // Byte Width

  // register signals
  logic           reg_we;
  logic           reg_re;
  logic [BlockAw-1:0]  reg_addr;
  logic [DW-1:0]  reg_wdata;
  logic [DBW-1:0] reg_be;
  logic [DW-1:0]  reg_rdata;
  logic           reg_error;

  logic          addrmiss, wr_err;

  logic [DW-1:0] reg_rdata_next;

  // Below register interface can be changed
  reg_req_t  reg_intf_req;
  reg_rsp_t  reg_intf_rsp;


  assign reg_intf_req = reg_req_i;
  assign reg_rsp_o = reg_intf_rsp;


  assign reg_we = reg_intf_req.valid & reg_intf_req.write;
  assign reg_re = reg_intf_req.valid & ~reg_intf_req.write;
  assign reg_addr = reg_intf_req.addr[BlockAw-1:0];
  assign reg_wdata = reg_intf_req.wdata;
  assign reg_be = reg_intf_req.wstrb;
  assign reg_intf_rsp.rdata = reg_rdata;
  assign reg_intf_rsp.error = reg_error;
  assign reg_intf_rsp.ready = 1'b1;

  assign reg_rdata = reg_rdata_next ;
  assign reg_error = (devmode_i & addrmiss) | wr_err;


  // Define SW related signals
  // Format: <reg>_<field>_{wd|we|qs}
  //        or <reg>_{wd|we|qs} if field == 1 or 0
  logic current_mode_independent_qs;
  logic current_mode_independent_re;
  logic current_mode_dual_qs;
  logic current_mode_dual_re;
  logic current_mode_triple_qs;
  logic current_mode_triple_re;
  logic [31:0] mismatches_qs;
  logic [31:0] mismatches_wd;
  logic mismatches_we;
  logic [31:0] sp_store_qs;
  logic [31:0] sp_store_wd;
  logic sp_store_we;

  // Register instances
  // R[current_mode]: V(True)

  //   F[independent]: 0:0
  prim_subreg_ext #(
    .DW    (1)
  ) u_current_mode_independent (
    .re     (current_mode_independent_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.current_mode.independent.d),
    .qre    (),
    .qe     (),
    .q      (),
    .qs     (current_mode_independent_qs)
  );


  //   F[dual]: 1:1
  prim_subreg_ext #(
    .DW    (1)
  ) u_current_mode_dual (
    .re     (current_mode_dual_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.current_mode.dual.d),
    .qre    (),
    .qe     (),
    .q      (),
    .qs     (current_mode_dual_qs)
  );


  //   F[triple]: 2:2
  prim_subreg_ext #(
    .DW    (1)
  ) u_current_mode_triple (
    .re     (current_mode_triple_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.current_mode.triple.d),
    .qre    (),
    .qe     (),
    .q      (),
    .qs     (current_mode_triple_qs)
  );


  // R[mismatches]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_mismatches (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (mismatches_we),
    .wd     (mismatches_wd),

    // from internal hardware
    .de     (hw2reg.mismatches.de),
    .d      (hw2reg.mismatches.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.mismatches.q ),

    // to register interface (read)
    .qs     (mismatches_qs)
  );


  // R[sp_store]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("RW"),
    .RESVAL  (32'h0)
  ) u_sp_store (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (sp_store_we),
    .wd     (sp_store_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0  ),

    // to internal hardware
    .qe     (reg2hw.sp_store.qe),
    .q      (reg2hw.sp_store.q ),

    // to register interface (read)
    .qs     (sp_store_qs)
  );




  logic [2:0] addr_hit;
  always_comb begin
    addr_hit = '0;
    addr_hit[0] = (reg_addr == HMR_CORE_REGS_CURRENT_MODE_OFFSET);
    addr_hit[1] = (reg_addr == HMR_CORE_REGS_MISMATCHES_OFFSET);
    addr_hit[2] = (reg_addr == HMR_CORE_REGS_SP_STORE_OFFSET);
  end

  assign addrmiss = (reg_re || reg_we) ? ~|addr_hit : 1'b0 ;

  // Check sub-word write is permitted
  always_comb begin
    wr_err = (reg_we &
              ((addr_hit[0] & (|(HMR_CORE_REGS_PERMIT[0] & ~reg_be))) |
               (addr_hit[1] & (|(HMR_CORE_REGS_PERMIT[1] & ~reg_be))) |
               (addr_hit[2] & (|(HMR_CORE_REGS_PERMIT[2] & ~reg_be)))));
  end

  assign current_mode_independent_re = addr_hit[0] & reg_re & !reg_error;

  assign current_mode_dual_re = addr_hit[0] & reg_re & !reg_error;

  assign current_mode_triple_re = addr_hit[0] & reg_re & !reg_error;

  assign mismatches_we = addr_hit[1] & reg_we & !reg_error;
  assign mismatches_wd = reg_wdata[31:0];

  assign sp_store_we = addr_hit[2] & reg_we & !reg_error;
  assign sp_store_wd = reg_wdata[31:0];

  // Read data return
  always_comb begin
    reg_rdata_next = '0;
    unique case (1'b1)
      addr_hit[0]: begin
        reg_rdata_next[0] = current_mode_independent_qs;
        reg_rdata_next[1] = current_mode_dual_qs;
        reg_rdata_next[2] = current_mode_triple_qs;
      end

      addr_hit[1]: begin
        reg_rdata_next[31:0] = mismatches_qs;
      end

      addr_hit[2]: begin
        reg_rdata_next[31:0] = sp_store_qs;
      end

      default: begin
        reg_rdata_next = '1;
      end
    endcase
  end

  // Unused signal tieoff

  // wdata / byte enable are not always fully used
  // add a blanket unused statement to handle lint waivers
  logic unused_wdata;
  logic unused_be;
  assign unused_wdata = ^reg_wdata;
  assign unused_be = ^reg_be;

  // Assertions for Register Interface
  `ASSERT(en2addrHit, (reg_we || reg_re) |-> $onehot0(addr_hit))

endmodule

module hmr_core_regs_reg_top_intf
#(
  parameter int AW = 4,
  localparam int DW = 32
) (
  input logic clk_i,
  input logic rst_ni,
  REG_BUS.in  regbus_slave,
  // To HW
  output hmr_core_regs_reg_pkg::hmr_core_regs_reg2hw_t reg2hw, // Write
  input  hmr_core_regs_reg_pkg::hmr_core_regs_hw2reg_t hw2reg, // Read
  // Config
  input devmode_i // If 1, explicit error return for unmapped register access
);
 localparam int unsigned STRB_WIDTH = DW/8;

`include "register_interface/typedef.svh"
`include "register_interface/assign.svh"

  // Define structs for reg_bus
  typedef logic [AW-1:0] addr_t;
  typedef logic [DW-1:0] data_t;
  typedef logic [STRB_WIDTH-1:0] strb_t;
  `REG_BUS_TYPEDEF_ALL(reg_bus, addr_t, data_t, strb_t)

  reg_bus_req_t s_reg_req;
  reg_bus_rsp_t s_reg_rsp;
  
  // Assign SV interface to structs
  `REG_BUS_ASSIGN_TO_REQ(s_reg_req, regbus_slave)
  `REG_BUS_ASSIGN_FROM_RSP(regbus_slave, s_reg_rsp)

  

  hmr_core_regs_reg_top #(
    .reg_req_t(reg_bus_req_t),
    .reg_rsp_t(reg_bus_rsp_t),
    .AW(AW)
  ) i_regs (
    .clk_i,
    .rst_ni,
    .reg_req_i(s_reg_req),
    .reg_rsp_o(s_reg_rsp),
    .reg2hw, // Write
    .hw2reg, // Read
    .devmode_i
  );
  
endmodule

