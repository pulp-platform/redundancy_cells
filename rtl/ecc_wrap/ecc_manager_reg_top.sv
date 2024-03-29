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
  input logic clk_i,
  input logic rst_ni,
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
  logic [31:0] mismatch_count_qs;
  logic [31:0] mismatch_count_wd;
  logic mismatch_count_we;
  logic [31:0] scrub_interval_qs;
  logic [31:0] scrub_interval_wd;
  logic scrub_interval_we;
  logic [31:0] scrub_fix_count_qs;
  logic [31:0] scrub_fix_count_wd;
  logic scrub_fix_count_we;
  logic [31:0] scrub_uncorrectable_count_qs;
  logic [31:0] scrub_uncorrectable_count_wd;
  logic scrub_uncorrectable_count_we;
  logic [31:0] write_mask_data_n_qs;
  logic [31:0] write_mask_data_n_wd;
  logic write_mask_data_n_we;
  logic [6:0] write_mask_ecc_n_qs;
  logic [6:0] write_mask_ecc_n_wd;
  logic write_mask_ecc_n_we;

  // Register instances
  // R[mismatch_count]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_mismatch_count (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (mismatch_count_we),
    .wd     (mismatch_count_wd),

    // from internal hardware
    .de     (hw2reg.mismatch_count.de),
    .d      (hw2reg.mismatch_count.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.mismatch_count.q ),

    // to register interface (read)
    .qs     (mismatch_count_qs)
  );


  // R[scrub_interval]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("RW"),
    .RESVAL  (32'h0)
  ) u_scrub_interval (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (scrub_interval_we),
    .wd     (scrub_interval_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0  ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.scrub_interval.q ),

    // to register interface (read)
    .qs     (scrub_interval_qs)
  );


  // R[scrub_fix_count]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_scrub_fix_count (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (scrub_fix_count_we),
    .wd     (scrub_fix_count_wd),

    // from internal hardware
    .de     (hw2reg.scrub_fix_count.de),
    .d      (hw2reg.scrub_fix_count.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.scrub_fix_count.q ),

    // to register interface (read)
    .qs     (scrub_fix_count_qs)
  );


  // R[scrub_uncorrectable_count]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("W0C"),
    .RESVAL  (32'h0)
  ) u_scrub_uncorrectable_count (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (scrub_uncorrectable_count_we),
    .wd     (scrub_uncorrectable_count_wd),

    // from internal hardware
    .de     (hw2reg.scrub_uncorrectable_count.de),
    .d      (hw2reg.scrub_uncorrectable_count.d ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.scrub_uncorrectable_count.q ),

    // to register interface (read)
    .qs     (scrub_uncorrectable_count_qs)
  );


  // R[write_mask_data_n]: V(False)

  prim_subreg #(
    .DW      (32),
    .SWACCESS("RW"),
    .RESVAL  (32'h0)
  ) u_write_mask_data_n (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (write_mask_data_n_we),
    .wd     (write_mask_data_n_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0  ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.write_mask_data_n.q ),

    // to register interface (read)
    .qs     (write_mask_data_n_qs)
  );


  // R[write_mask_ecc_n]: V(False)

  prim_subreg #(
    .DW      (7),
    .SWACCESS("RW"),
    .RESVAL  (7'h0)
  ) u_write_mask_ecc_n (
    .clk_i   (clk_i    ),
    .rst_ni  (rst_ni  ),

    // from register interface
    .we     (write_mask_ecc_n_we),
    .wd     (write_mask_ecc_n_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0  ),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.write_mask_ecc_n.q ),

    // to register interface (read)
    .qs     (write_mask_ecc_n_qs)
  );




  logic [5:0] addr_hit;
  always_comb begin
    addr_hit = '0;
    addr_hit[0] = (reg_addr == ECC_MANAGER_MISMATCH_COUNT_OFFSET);
    addr_hit[1] = (reg_addr == ECC_MANAGER_SCRUB_INTERVAL_OFFSET);
    addr_hit[2] = (reg_addr == ECC_MANAGER_SCRUB_FIX_COUNT_OFFSET);
    addr_hit[3] = (reg_addr == ECC_MANAGER_SCRUB_UNCORRECTABLE_COUNT_OFFSET);
    addr_hit[4] = (reg_addr == ECC_MANAGER_WRITE_MASK_DATA_N_OFFSET);
    addr_hit[5] = (reg_addr == ECC_MANAGER_WRITE_MASK_ECC_N_OFFSET);
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

  assign mismatch_count_we = addr_hit[0] & reg_we & !reg_error;
  assign mismatch_count_wd = reg_wdata[31:0];

  assign scrub_interval_we = addr_hit[1] & reg_we & !reg_error;
  assign scrub_interval_wd = reg_wdata[31:0];

  assign scrub_fix_count_we = addr_hit[2] & reg_we & !reg_error;
  assign scrub_fix_count_wd = reg_wdata[31:0];

  assign scrub_uncorrectable_count_we = addr_hit[3] & reg_we & !reg_error;
  assign scrub_uncorrectable_count_wd = reg_wdata[31:0];

  assign write_mask_data_n_we = addr_hit[4] & reg_we & !reg_error;
  assign write_mask_data_n_wd = reg_wdata[31:0];

  assign write_mask_ecc_n_we = addr_hit[5] & reg_we & !reg_error;
  assign write_mask_ecc_n_wd = reg_wdata[6:0];

  // Read data return
  always_comb begin
    reg_rdata_next = '0;
    unique case (1'b1)
      addr_hit[0]: begin
        reg_rdata_next[31:0] = mismatch_count_qs;
      end

      addr_hit[1]: begin
        reg_rdata_next[31:0] = scrub_interval_qs;
      end

      addr_hit[2]: begin
        reg_rdata_next[31:0] = scrub_fix_count_qs;
      end

      addr_hit[3]: begin
        reg_rdata_next[31:0] = scrub_uncorrectable_count_qs;
      end

      addr_hit[4]: begin
        reg_rdata_next[31:0] = write_mask_data_n_qs;
      end

      addr_hit[5]: begin
        reg_rdata_next[6:0] = write_mask_ecc_n_qs;
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

module ecc_manager_reg_top_intf
#(
  parameter int AW = 5,
  localparam int DW = 32
) (
  input logic clk_i,
  input logic rst_ni,
  REG_BUS.in  regbus_slave,
  // To HW
  output ecc_manager_reg_pkg::ecc_manager_reg2hw_t reg2hw, // Write
  input  ecc_manager_reg_pkg::ecc_manager_hw2reg_t hw2reg, // Read
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

  

  ecc_manager_reg_top #(
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


