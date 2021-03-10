# Redundancy Cells

This repository contains various modules used to add redundancy.

## ECC encoders and decoders
ECC encoders and decoders are imported using lowRISC's `vendor.py` script. To re-import and re-generate the `prim_secded_` modules run
```bash
make gen_ECC
```

## ECC wrapper for SRAM
`ecc_sram_wrap.sv` is a wrapper for the tc_sram tech_cell to add ecc in a customizable fashion. It interfaces a modified `TCDM_BANK_MEM_BUS.Slave` defined in pulp_soc with the memory, implementing a load-and-store architecture for writes where not the full word is written. As this requires an additional cycle, a gnt signal is exposed, delaying the subsequent transaction if necessary.

## ECC translators for data bus interfaces
The `BUS_enc_dec` encoders and decoders add or remove ECC to the parametrized `XBAR_TCDM_BUS`, `XBAR_PE_BUS`, and `XBAR_DEMUX_BUS`, defined in [pulp_interfaces.sv](https://github.com/micprog/pulp_soc/blob/ibex_update/rtl/components/pulp_interfaces.sv), as well as [`AXI_BUS`](https://github.com/pulp-platfrom/axi).

## Triple Modular Redundancy majority voters
The `TMR_voter`s are Triple Modular Redundancy majority voters, based on research indicated in the corresponding files. To detect the failing module, additional signals are implemented in higher-level modules.

## Configurable Triple Core Lock-Step Unit (cTCLS_unit)
TODO documentation

To re-generate regfile, run following command in the root directory of this repo.
```bash
make gen_cTCLS
```
This will generate the register file SV-code, its corresponding C-code and documentation using lowrisc's reggen tool via the pulp register-interface repository.

## Testing
To run tests, execute the following command:
```bash
./run_tests.sh
```

A bender installation >=v0.22 is required.
