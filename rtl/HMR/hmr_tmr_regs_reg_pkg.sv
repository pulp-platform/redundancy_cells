// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Package auto-generated by `reggen` containing data structure

package hmr_tmr_regs_reg_pkg;

  // Address widths within the block
  parameter int BlockAw = 3;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic        q;
    logic        qe;
  } hmr_tmr_regs_reg2hw_tmr_enable_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } delay_resynch;
    struct packed {
      logic        q;
      logic        qe;
    } setback;
    struct packed {
      logic        q;
      logic        qe;
    } reload_setback;
    struct packed {
      logic        q;
      logic        qe;
    } rapid_recovery;
    struct packed {
      logic        q;
      logic        qe;
    } force_resynch;
    struct packed {
      logic        q;
      logic        qe;
    } synch_req;
  } hmr_tmr_regs_reg2hw_tmr_config_reg_t;

  typedef struct packed {
    logic        d;
    logic        de;
  } hmr_tmr_regs_hw2reg_tmr_enable_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
      logic        de;
    } delay_resynch;
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
    } rapid_recovery;
    struct packed {
      logic        d;
      logic        de;
    } force_resynch;
    struct packed {
      logic        d;
      logic        de;
    } synch_req;
  } hmr_tmr_regs_hw2reg_tmr_config_reg_t;

  // Register -> HW type
  typedef struct packed {
    hmr_tmr_regs_reg2hw_tmr_enable_reg_t tmr_enable; // [13:12]
    hmr_tmr_regs_reg2hw_tmr_config_reg_t tmr_config; // [11:0]
  } hmr_tmr_regs_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    hmr_tmr_regs_hw2reg_tmr_enable_reg_t tmr_enable; // [13:12]
    hmr_tmr_regs_hw2reg_tmr_config_reg_t tmr_config; // [11:0]
  } hmr_tmr_regs_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] HMR_TMR_REGS_TMR_ENABLE_OFFSET = 3'h 0;
  parameter logic [BlockAw-1:0] HMR_TMR_REGS_TMR_CONFIG_OFFSET = 3'h 4;

  // Register index
  typedef enum int {
    HMR_TMR_REGS_TMR_ENABLE,
    HMR_TMR_REGS_TMR_CONFIG
  } hmr_tmr_regs_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] HMR_TMR_REGS_PERMIT [2] = '{
    4'b 0001, // index[0] HMR_TMR_REGS_TMR_ENABLE
    4'b 0001  // index[1] HMR_TMR_REGS_TMR_CONFIG
  };

endpackage

