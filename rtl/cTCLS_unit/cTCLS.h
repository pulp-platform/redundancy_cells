// Generated register defines for cTCLS_manager

#ifndef _CTCLS_MANAGER_REG_DEFS_
#define _CTCLS_MANAGER_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Register width
#define CTCLS_MANAGER_PARAM_REG_WIDTH 32

// Common Interrupt Offsets

// Redundancy Mode configuration
#define CTCLS_MANAGER_MODE(id) (CTCLS_MANAGER##id##_BASE_ADDR + 0x0)
#define CTCLS_MANAGER_MODE_REG_OFFSET 0x0
#define CTCLS_MANAGER_MODE_MODE 0
#define CTCLS_MANAGER_MODE_RESTORE_MODE 8

// Mismatches of core 0
#define CTCLS_MANAGER_MISMATCHES_0(id) (CTCLS_MANAGER##id##_BASE_ADDR + 0x4)
#define CTCLS_MANAGER_MISMATCHES_0_REG_OFFSET 0x4

// Mismatches of core 1
#define CTCLS_MANAGER_MISMATCHES_1(id) (CTCLS_MANAGER##id##_BASE_ADDR + 0x8)
#define CTCLS_MANAGER_MISMATCHES_1_REG_OFFSET 0x8

// Mismatches of core 2
#define CTCLS_MANAGER_MISMATCHES_2(id) (CTCLS_MANAGER##id##_BASE_ADDR + 0xc)
#define CTCLS_MANAGER_MISMATCHES_2_REG_OFFSET 0xc

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _CTCLS_MANAGER_REG_DEFS_
// End generated register defines for cTCLS_manager
