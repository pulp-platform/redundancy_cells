// Generated register defines for ECC_manager

#ifndef _ECC_MANAGER_REG_DEFS_
#define _ECC_MANAGER_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
#define ECC_MANAGER_PARAM_NUM_BANKS 6

// Register width
#define ECC_MANAGER_PARAM_REG_WIDTH 32

// Correctable mismatches caught by ecc on access (common parameters)
#define ECC_MANAGER_MISMATCH_COUNT_CORRECTABLE_MISMATCHES_FIELD_WIDTH 32
#define ECC_MANAGER_MISMATCH_COUNT_CORRECTABLE_MISMATCHES_FIELDS_PER_REG 1
#define ECC_MANAGER_MISMATCH_COUNT_MULTIREG_COUNT 6

// Correctable mismatches caught by ecc on access
#define ECC_MANAGER_MISMATCH_COUNT_0_REG_OFFSET 0x0

// Correctable mismatches caught by ecc on access
#define ECC_MANAGER_MISMATCH_COUNT_1_REG_OFFSET 0x4

// Correctable mismatches caught by ecc on access
#define ECC_MANAGER_MISMATCH_COUNT_2_REG_OFFSET 0x8

// Correctable mismatches caught by ecc on access
#define ECC_MANAGER_MISMATCH_COUNT_3_REG_OFFSET 0xc

// Correctable mismatches caught by ecc on access
#define ECC_MANAGER_MISMATCH_COUNT_4_REG_OFFSET 0x10

// Correctable mismatches caught by ecc on access
#define ECC_MANAGER_MISMATCH_COUNT_5_REG_OFFSET 0x14

// Interval between scrubs
#define ECC_MANAGER_SCRUB_INTERVAL_REG_OFFSET 0x18

// Correctable mismatches caught by ecc on scrub (common parameters)
#define ECC_MANAGER_SCRUB_FIX_COUNT_CORRECTABLE_MISMATCHES_FIELD_WIDTH 32
#define ECC_MANAGER_SCRUB_FIX_COUNT_CORRECTABLE_MISMATCHES_FIELDS_PER_REG 1
#define ECC_MANAGER_SCRUB_FIX_COUNT_MULTIREG_COUNT 6

// Correctable mismatches caught by ecc on scrub
#define ECC_MANAGER_SCRUB_FIX_COUNT_0_REG_OFFSET 0x1c

// Correctable mismatches caught by ecc on scrub
#define ECC_MANAGER_SCRUB_FIX_COUNT_1_REG_OFFSET 0x20

// Correctable mismatches caught by ecc on scrub
#define ECC_MANAGER_SCRUB_FIX_COUNT_2_REG_OFFSET 0x24

// Correctable mismatches caught by ecc on scrub
#define ECC_MANAGER_SCRUB_FIX_COUNT_3_REG_OFFSET 0x28

// Correctable mismatches caught by ecc on scrub
#define ECC_MANAGER_SCRUB_FIX_COUNT_4_REG_OFFSET 0x2c

// Correctable mismatches caught by ecc on scrub
#define ECC_MANAGER_SCRUB_FIX_COUNT_5_REG_OFFSET 0x30

// Testing: Inverted write mask for data bits (common parameters)
#define ECC_MANAGER_WRITE_MASK_DATA_N_WRITE_MASK_DATA_N_FIELD_WIDTH 32
#define ECC_MANAGER_WRITE_MASK_DATA_N_WRITE_MASK_DATA_N_FIELDS_PER_REG 1
#define ECC_MANAGER_WRITE_MASK_DATA_N_MULTIREG_COUNT 6

// Testing: Inverted write mask for data bits
#define ECC_MANAGER_WRITE_MASK_DATA_N_0_REG_OFFSET 0x34

// Testing: Inverted write mask for data bits
#define ECC_MANAGER_WRITE_MASK_DATA_N_1_REG_OFFSET 0x38

// Testing: Inverted write mask for data bits
#define ECC_MANAGER_WRITE_MASK_DATA_N_2_REG_OFFSET 0x3c

// Testing: Inverted write mask for data bits
#define ECC_MANAGER_WRITE_MASK_DATA_N_3_REG_OFFSET 0x40

// Testing: Inverted write mask for data bits
#define ECC_MANAGER_WRITE_MASK_DATA_N_4_REG_OFFSET 0x44

// Testing: Inverted write mask for data bits
#define ECC_MANAGER_WRITE_MASK_DATA_N_5_REG_OFFSET 0x48

// Testing: Inverted write mask for ECC bits (common parameters)
#define ECC_MANAGER_WRITE_MASK_ECC_N_WRITE_MASK_ECC_N_FIELD_WIDTH 7
#define ECC_MANAGER_WRITE_MASK_ECC_N_WRITE_MASK_ECC_N_FIELDS_PER_REG 4
#define ECC_MANAGER_WRITE_MASK_ECC_N_MULTIREG_COUNT 2

// Testing: Inverted write mask for ECC bits
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_REG_OFFSET 0x4c
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_0_MASK 0x7f
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_0_OFFSET 0
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_0_FIELD \
  ((bitfield_field32_t) { .mask = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_0_MASK, .index = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_0_OFFSET })
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_1_MASK 0x7f
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_1_OFFSET 7
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_1_FIELD \
  ((bitfield_field32_t) { .mask = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_1_MASK, .index = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_1_OFFSET })
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_2_MASK 0x7f
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_2_OFFSET 14
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_2_FIELD \
  ((bitfield_field32_t) { .mask = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_2_MASK, .index = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_2_OFFSET })
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_3_MASK 0x7f
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_3_OFFSET 21
#define ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_3_FIELD \
  ((bitfield_field32_t) { .mask = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_3_MASK, .index = ECC_MANAGER_WRITE_MASK_ECC_N_0_WRITE_MASK_ECC_N_3_OFFSET })

// Testing: Inverted write mask for ECC bits
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_REG_OFFSET 0x50
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_4_MASK 0x7f
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_4_OFFSET 0
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_4_FIELD \
  ((bitfield_field32_t) { .mask = ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_4_MASK, .index = ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_4_OFFSET })
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_5_MASK 0x7f
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_5_OFFSET 7
#define ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_5_FIELD \
  ((bitfield_field32_t) { .mask = ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_5_MASK, .index = ECC_MANAGER_WRITE_MASK_ECC_N_1_WRITE_MASK_ECC_N_5_OFFSET })

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _ECC_MANAGER_REG_DEFS_
// End generated register defines for ECC_manager