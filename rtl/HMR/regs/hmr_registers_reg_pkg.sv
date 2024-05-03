// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Package auto-generated by `reggen` containing data structure

package hmr_registers_reg_pkg;

  // Param list
  parameter int NumCores = 12;
  parameter int NumDMRGroups = 6;
  parameter int NumTMRGroups = 4;

  // Address widths within the block
  parameter int BlockAw = 5;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic [5:0]  q;
    logic        qe;
  } hmr_registers_reg2hw_dmr_enable_reg_t;

  typedef struct packed {
    logic [3:0]  q;
    logic        qe;
  } hmr_registers_reg2hw_tmr_enable_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } rapid_recovery;
    struct packed {
      logic        q;
      logic        qe;
    } force_recovery;
    struct packed {
      logic        q;
      logic        qe;
    } setback;
    struct packed {
      logic        q;
      logic        qe;
    } synch_req;
  } hmr_registers_reg2hw_dmr_config_reg_t;

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
  } hmr_registers_reg2hw_tmr_config_reg_t;

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
    struct packed {
      logic        d;
    } rapid_recovery;
  } hmr_registers_hw2reg_avail_config_reg_t;

  typedef struct packed {
    logic [11:0] d;
  } hmr_registers_hw2reg_cores_en_reg_t;

  typedef struct packed {
    logic [5:0]  d;
  } hmr_registers_hw2reg_dmr_enable_reg_t;

  typedef struct packed {
    logic [3:0]  d;
  } hmr_registers_hw2reg_tmr_enable_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
    } rapid_recovery;
    struct packed {
      logic        d;
    } force_recovery;
    struct packed {
      logic        d;
    } setback;
    struct packed {
      logic        d;
    } synch_req;
  } hmr_registers_hw2reg_dmr_config_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
    } delay_resynch;
    struct packed {
      logic        d;
    } setback;
    struct packed {
      logic        d;
    } reload_setback;
    struct packed {
      logic        d;
    } rapid_recovery;
    struct packed {
      logic        d;
    } force_resynch;
    struct packed {
      logic        d;
    } synch_req;
  } hmr_registers_hw2reg_tmr_config_reg_t;

  // Register -> HW type
  typedef struct packed {
    hmr_registers_reg2hw_dmr_enable_reg_t dmr_enable; // [31:25]
    hmr_registers_reg2hw_tmr_enable_reg_t tmr_enable; // [24:20]
    hmr_registers_reg2hw_dmr_config_reg_t dmr_config; // [19:12]
    hmr_registers_reg2hw_tmr_config_reg_t tmr_config; // [11:0]
  } hmr_registers_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    hmr_registers_hw2reg_avail_config_reg_t avail_config; // [35:32]
    hmr_registers_hw2reg_cores_en_reg_t cores_en; // [31:20]
    hmr_registers_hw2reg_dmr_enable_reg_t dmr_enable; // [19:14]
    hmr_registers_hw2reg_tmr_enable_reg_t tmr_enable; // [13:10]
    hmr_registers_hw2reg_dmr_config_reg_t dmr_config; // [9:6]
    hmr_registers_hw2reg_tmr_config_reg_t tmr_config; // [5:0]
  } hmr_registers_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] HMR_REGISTERS_AVAIL_CONFIG_OFFSET = 5'h 0;
  parameter logic [BlockAw-1:0] HMR_REGISTERS_CORES_EN_OFFSET = 5'h 4;
  parameter logic [BlockAw-1:0] HMR_REGISTERS_DMR_ENABLE_OFFSET = 5'h 8;
  parameter logic [BlockAw-1:0] HMR_REGISTERS_TMR_ENABLE_OFFSET = 5'h c;
  parameter logic [BlockAw-1:0] HMR_REGISTERS_DMR_CONFIG_OFFSET = 5'h 10;
  parameter logic [BlockAw-1:0] HMR_REGISTERS_TMR_CONFIG_OFFSET = 5'h 14;

  // Reset values for hwext registers and their fields
  parameter logic [8:0] HMR_REGISTERS_AVAIL_CONFIG_RESVAL = 9'h 0;
  parameter logic [11:0] HMR_REGISTERS_CORES_EN_RESVAL = 12'h 0;
  parameter logic [5:0] HMR_REGISTERS_DMR_ENABLE_RESVAL = 6'h 0;
  parameter logic [5:0] HMR_REGISTERS_DMR_ENABLE_DMR_ENABLE_RESVAL = 6'h 0;
  parameter logic [3:0] HMR_REGISTERS_TMR_ENABLE_RESVAL = 4'h 0;
  parameter logic [3:0] HMR_REGISTERS_TMR_ENABLE_TMR_ENABLE_RESVAL = 4'h 0;
  parameter logic [3:0] HMR_REGISTERS_DMR_CONFIG_RESVAL = 4'h c;
  parameter logic [0:0] HMR_REGISTERS_DMR_CONFIG_SETBACK_RESVAL = 1'h 1;
  parameter logic [0:0] HMR_REGISTERS_DMR_CONFIG_SYNCH_REQ_RESVAL = 1'h 1;
  parameter logic [5:0] HMR_REGISTERS_TMR_CONFIG_RESVAL = 6'h 26;
  parameter logic [0:0] HMR_REGISTERS_TMR_CONFIG_DELAY_RESYNCH_RESVAL = 1'h 0;
  parameter logic [0:0] HMR_REGISTERS_TMR_CONFIG_SETBACK_RESVAL = 1'h 1;
  parameter logic [0:0] HMR_REGISTERS_TMR_CONFIG_RELOAD_SETBACK_RESVAL = 1'h 1;
  parameter logic [0:0] HMR_REGISTERS_TMR_CONFIG_FORCE_RESYNCH_RESVAL = 1'h 0;
  parameter logic [0:0] HMR_REGISTERS_TMR_CONFIG_SYNCH_REQ_RESVAL = 1'h 1;

  // Register index
  typedef enum int {
    HMR_REGISTERS_AVAIL_CONFIG,
    HMR_REGISTERS_CORES_EN,
    HMR_REGISTERS_DMR_ENABLE,
    HMR_REGISTERS_TMR_ENABLE,
    HMR_REGISTERS_DMR_CONFIG,
    HMR_REGISTERS_TMR_CONFIG
  } hmr_registers_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] HMR_REGISTERS_PERMIT [6] = '{
    4'b 0011, // index[0] HMR_REGISTERS_AVAIL_CONFIG
    4'b 0011, // index[1] HMR_REGISTERS_CORES_EN
    4'b 0001, // index[2] HMR_REGISTERS_DMR_ENABLE
    4'b 0001, // index[3] HMR_REGISTERS_TMR_ENABLE
    4'b 0001, // index[4] HMR_REGISTERS_DMR_CONFIG
    4'b 0001  // index[5] HMR_REGISTERS_TMR_CONFIG
  };

endpackage

