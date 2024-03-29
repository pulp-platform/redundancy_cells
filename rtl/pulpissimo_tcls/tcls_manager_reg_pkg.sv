// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Package auto-generated by `reggen` containing data structure

package tcls_manager_reg_pkg;

  // Address widths within the block
  parameter int BlockAw = 5;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } tcls_manager_reg2hw_sp_store_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } setback;
    struct packed {
      logic        q;
    } reload_setback;
    struct packed {
      logic        q;
    } force_resynch;
  } tcls_manager_reg2hw_tcls_config_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } tcls_manager_reg2hw_mismatches_0_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } tcls_manager_reg2hw_mismatches_1_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } tcls_manager_reg2hw_mismatches_2_reg_t;

  typedef struct packed {
    logic [31:0] d;
    logic        de;
  } tcls_manager_hw2reg_sp_store_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
      logic        de;
    } setback;
    struct packed {
      logic        d;
      logic        de;
    } reload_setback;
    struct packed {
      logic        d;
      logic        de;
    } force_resynch;
  } tcls_manager_hw2reg_tcls_config_reg_t;

  typedef struct packed {
    logic [31:0] d;
    logic        de;
  } tcls_manager_hw2reg_mismatches_0_reg_t;

  typedef struct packed {
    logic [31:0] d;
    logic        de;
  } tcls_manager_hw2reg_mismatches_1_reg_t;

  typedef struct packed {
    logic [31:0] d;
    logic        de;
  } tcls_manager_hw2reg_mismatches_2_reg_t;

  // Register -> HW type
  typedef struct packed {
    tcls_manager_reg2hw_sp_store_reg_t sp_store; // [131:99]
    tcls_manager_reg2hw_tcls_config_reg_t tcls_config; // [98:96]
    tcls_manager_reg2hw_mismatches_0_reg_t mismatches_0; // [95:64]
    tcls_manager_reg2hw_mismatches_1_reg_t mismatches_1; // [63:32]
    tcls_manager_reg2hw_mismatches_2_reg_t mismatches_2; // [31:0]
  } tcls_manager_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    tcls_manager_hw2reg_sp_store_reg_t sp_store; // [137:105]
    tcls_manager_hw2reg_tcls_config_reg_t tcls_config; // [104:99]
    tcls_manager_hw2reg_mismatches_0_reg_t mismatches_0; // [98:66]
    tcls_manager_hw2reg_mismatches_1_reg_t mismatches_1; // [65:33]
    tcls_manager_hw2reg_mismatches_2_reg_t mismatches_2; // [32:0]
  } tcls_manager_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] TCLS_MANAGER_SP_STORE_OFFSET = 5'h 0;
  parameter logic [BlockAw-1:0] TCLS_MANAGER_TCLS_CONFIG_OFFSET = 5'h 4;
  parameter logic [BlockAw-1:0] TCLS_MANAGER_MISMATCHES_0_OFFSET = 5'h 8;
  parameter logic [BlockAw-1:0] TCLS_MANAGER_MISMATCHES_1_OFFSET = 5'h c;
  parameter logic [BlockAw-1:0] TCLS_MANAGER_MISMATCHES_2_OFFSET = 5'h 10;

  // Register index
  typedef enum int {
    TCLS_MANAGER_SP_STORE,
    TCLS_MANAGER_TCLS_CONFIG,
    TCLS_MANAGER_MISMATCHES_0,
    TCLS_MANAGER_MISMATCHES_1,
    TCLS_MANAGER_MISMATCHES_2
  } tcls_manager_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] TCLS_MANAGER_PERMIT [5] = '{
    4'b 1111, // index[0] TCLS_MANAGER_SP_STORE
    4'b 0001, // index[1] TCLS_MANAGER_TCLS_CONFIG
    4'b 1111, // index[2] TCLS_MANAGER_MISMATCHES_0
    4'b 1111, // index[3] TCLS_MANAGER_MISMATCHES_1
    4'b 1111  // index[4] TCLS_MANAGER_MISMATCHES_2
  };

endpackage

