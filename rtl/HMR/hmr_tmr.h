// Generated register defines for HMR_tmr_regs

#ifndef _HMR_TMR_REGS_REG_DEFS_
#define _HMR_TMR_REGS_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Register width
#define HMR_TMR_REGS_PARAM_REG_WIDTH 32

// TMR configuration enable.
#define HMR_TMR_REGS_TMR_ENABLE_REG_OFFSET 0x0
#define HMR_TMR_REGS_TMR_ENABLE_TMR_ENABLE_BIT 0

// TMR configuration bits.
#define HMR_TMR_REGS_TMR_CONFIG_REG_OFFSET 0x4
#define HMR_TMR_REGS_TMR_CONFIG_DELAY_RESYNCH_BIT 0
#define HMR_TMR_REGS_TMR_CONFIG_SETBACK_BIT 1
#define HMR_TMR_REGS_TMR_CONFIG_RELOAD_SETBACK_BIT 2
#define HMR_TMR_REGS_TMR_CONFIG_FORCE_RESYNCH_BIT 3

// Stack Pointer storage register
#define HMR_TMR_REGS_SP_STORE_REG_OFFSET 0x8

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _HMR_TMR_REGS_REG_DEFS_
// End generated register defines for HMR_tmr_regs