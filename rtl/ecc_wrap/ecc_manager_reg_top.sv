// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Top module auto-generated by `reggen`


`include "common_cells/assertions.svh"

module ecc_manager_reg_top #(
    parameter type reg_req_t = logic,
    parameter type reg_rsp_t = logic,
    parameter int AW = 5
) (
  input clk_i,
  input rst_ni,
  input  reg_req_t reg_req_i,
  output reg_rsp_t reg_rsp_o,
  // To HW
  output ecc_manager_reg_pkg::ecc_manager_reg2hw_t reg2hw, // Write
  input  ecc_manager_reg_pkg::ecc_manager_hw2reg_t hw2reg, // Read


  // Config
  input devmode_i // If 1, explicit error return for unmapped register access
);

  import ecc_manager_reg_pkg::* ;

  localparam int DW = 32;
  localparam int DBW = DW/8;                    // Byte Width

  // register signals
  logic           reg_we;
  logic           reg_re;
  logic [AW-1:0]  reg_addr;
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
  assign reg_addr = reg_intf_req.addr;
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
  logic [31:0] private0_qs;
  logic [31:0] private0_wd;
  logic private0_we;
  logic [31:0] private1_qs;
  logic [31:0] private1_wd;
  logic private1_we;
  logic [31:0] cuts0_qs;
  logic [31:0] cuts0_wd;
  logic cuts0_we;
  logic [31:0] cuts1_qs;
  logic [31:0] cuts1_wd;
  logic cuts1_we;
  logic [31:0] cuts2_qs;
  logic [31:0] cuts2_wd;
  logic cuts2_we;
  logic [31:0] cuts3_qs;
  logic [31:0] cuts3_wd;
  logic cuts3_we;

  // Register instances
  // R[private0]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_private0 (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (private0_we),
    .wd     (private0_wd),

    // from internal hardware
    .de     (hw2reg.private0.de),
    .d      (hw2reg.private0.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.private0.q ),

    // to register interface (read)
    .qs     (private0_qs)
  );


  // R[private1]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_private1 (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (private1_we),
    .wd     (private1_wd),

    // from internal hardware
    .de     (hw2reg.private1.de),
    .d      (hw2reg.private1.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.private1.q ),

    // to register interface (read)
    .qs     (private1_qs)
  );


  // R[cuts0]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_cuts0 (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (cuts0_we),
    .wd     (cuts0_wd),

    // from internal hardware
    .de     (hw2reg.cuts0.de),
    .d      (hw2reg.cuts0.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cuts0.q ),

    // to register interface (read)
    .qs     (cuts0_qs)
  );


  // R[cuts1]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_cuts1 (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (cuts1_we),
    .wd     (cuts1_wd),

    // from internal hardware
    .de     (hw2reg.cuts1.de),
    .d      (hw2reg.cuts1.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cuts1.q ),

    // to register interface (read)
    .qs     (cuts1_qs)
  );


  // R[cuts2]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_cuts2 (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (cuts2_we),
    .wd     (cuts2_wd),

    // from internal hardware
    .de     (hw2reg.cuts2.de),
    .d      (hw2reg.cuts2.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cuts2.q ),

    // to register interface (read)
    .qs     (cuts2_qs)
  );


  // R[cuts3]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_cuts3 (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (cuts3_we),
    .wd     (cuts3_wd),

    // from internal hardware
    .de     (hw2reg.cuts3.de),
    .d      (hw2reg.cuts3.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cuts3.q ),

    // to register interface (read)
    .qs     (cuts3_qs)
  );




  logic [5:0] addr_hit;
  always_comb begin
    addr_hit = '0;
    addr_hit[0] = (reg_addr == ECC_MANAGER_PRIVATE0_OFFSET);
    addr_hit[1] = (reg_addr == ECC_MANAGER_PRIVATE1_OFFSET);
    addr_hit[2] = (reg_addr == ECC_MANAGER_CUTS0_OFFSET);
    addr_hit[3] = (reg_addr == ECC_MANAGER_CUTS1_OFFSET);
    addr_hit[4] = (reg_addr == ECC_MANAGER_CUTS2_OFFSET);
    addr_hit[5] = (reg_addr == ECC_MANAGER_CUTS3_OFFSET);
  end

  assign addrmiss = (reg_re || reg_we) ? ~|addr_hit : 1'b0 ;

  // Check sub-word write is permitted
  always_comb begin
    wr_err = (reg_we &
              ((addr_hit[0] & (|(ECC_MANAGER_PERMIT[0] & ~reg_be))) |
               (addr_hit[1] & (|(ECC_MANAGER_PERMIT[1] & ~reg_be))) |
               (addr_hit[2] & (|(ECC_MANAGER_PERMIT[2] & ~reg_be))) |
               (addr_hit[3] & (|(ECC_MANAGER_PERMIT[3] & ~reg_be))) |
               (addr_hit[4] & (|(ECC_MANAGER_PERMIT[4] & ~reg_be))) |
               (addr_hit[5] & (|(ECC_MANAGER_PERMIT[5] & ~reg_be)))));
  end

  assign private0_we = addr_hit[0] & reg_we & !reg_error;
  assign private0_wd = reg_wdata[31:0];

  assign private1_we = addr_hit[1] & reg_we & !reg_error;
  assign private1_wd = reg_wdata[31:0];

  assign cuts0_we = addr_hit[2] & reg_we & !reg_error;
  assign cuts0_wd = reg_wdata[31:0];

  assign cuts1_we = addr_hit[3] & reg_we & !reg_error;
  assign cuts1_wd = reg_wdata[31:0];

  assign cuts2_we = addr_hit[4] & reg_we & !reg_error;
  assign cuts2_wd = reg_wdata[31:0];

  assign cuts3_we = addr_hit[5] & reg_we & !reg_error;
  assign cuts3_wd = reg_wdata[31:0];

  // Read data return
  always_comb begin
    reg_rdata_next = '0;
    unique case (1'b1)
      addr_hit[0]: begin
        reg_rdata_next[31:0] = private0_qs;
      end

      addr_hit[1]: begin
        reg_rdata_next[31:0] = private1_qs;
      end

      addr_hit[2]: begin
        reg_rdata_next[31:0] = cuts0_qs;
      end

      addr_hit[3]: begin
        reg_rdata_next[31:0] = cuts1_qs;
      end

      addr_hit[4]: begin
        reg_rdata_next[31:0] = cuts2_qs;
      end

      addr_hit[5]: begin
        reg_rdata_next[31:0] = cuts3_qs;
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
