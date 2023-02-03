// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Package auto-generated by `reggen` containing data structure

package hmr_core_regs_reg_pkg;

  // Address widths within the block
  parameter int BlockAw = 4;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic [31:0] q;
  } hmr_core_regs_reg2hw_mismatches_reg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } hmr_core_regs_reg2hw_sp_store_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
    } independent;
    struct packed {
      logic        d;
    } dual;
    struct packed {
      logic        d;
    } triple;
  } hmr_core_regs_hw2reg_current_mode_reg_t;

  typedef struct packed {
    logic [31:0] d;
    logic        de;
  } hmr_core_regs_hw2reg_mismatches_reg_t;

  // Register -> HW type
  typedef struct packed {
    hmr_core_regs_reg2hw_mismatches_reg_t mismatches; // [64:33]
    hmr_core_regs_reg2hw_sp_store_reg_t sp_store; // [32:0]
  } hmr_core_regs_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    hmr_core_regs_hw2reg_current_mode_reg_t current_mode; // [35:33]
    hmr_core_regs_hw2reg_mismatches_reg_t mismatches; // [32:0]
  } hmr_core_regs_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] HMR_CORE_REGS_CURRENT_MODE_OFFSET = 4'h 0;
  parameter logic [BlockAw-1:0] HMR_CORE_REGS_MISMATCHES_OFFSET = 4'h 4;
  parameter logic [BlockAw-1:0] HMR_CORE_REGS_SP_STORE_OFFSET = 4'h 8;

  // Reset values for hwext registers and their fields
  parameter logic [2:0] HMR_CORE_REGS_CURRENT_MODE_RESVAL = 3'h 1;
  parameter logic [0:0] HMR_CORE_REGS_CURRENT_MODE_INDEPENDENT_RESVAL = 1'h 1;
  parameter logic [0:0] HMR_CORE_REGS_CURRENT_MODE_DUAL_RESVAL = 1'h 0;
  parameter logic [0:0] HMR_CORE_REGS_CURRENT_MODE_TRIPLE_RESVAL = 1'h 0;

  // Register index
  typedef enum int {
    HMR_CORE_REGS_CURRENT_MODE,
    HMR_CORE_REGS_MISMATCHES,
    HMR_CORE_REGS_SP_STORE
  } hmr_core_regs_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] HMR_CORE_REGS_PERMIT [3] = '{
    4'b 0001, // index[0] HMR_CORE_REGS_CURRENT_MODE
    4'b 1111, // index[1] HMR_CORE_REGS_MISMATCHES
    4'b 1111  // index[2] HMR_CORE_REGS_SP_STORE
  };

endpackage

