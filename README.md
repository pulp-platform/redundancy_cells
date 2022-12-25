# Redundancy Cells

This repository contains various modules used to add redundancy.

## On-Demand Redundancy Grouping (ODRG_unit)
The `ODRG_unit` is designed as a configurable bridge between three ibex cores, allowing for independent operation or lock-step operation with majority voting, triggering an interrupt in case a mismatch is detected. It uses lowrisc's reggen tool to generate the required configuration registers.

### Testing
ODRG is integrated in the [PULP cluster](https://github.com/pulp-platform/pulp_cluster/tree/space_pulp) and the [PULP](https://github.com/pulp-platform/pulp/tree/space_pulp) system. To test, please use the `space_pulp` branch.

### Citing
If you are using ODRG in yout academic work you can cite us:
```BibTeX
@misc{https://doi.org/10.48550/arxiv.2205.12580,
  doi = {10.48550/ARXIV.2205.12580},
  url = {https://arxiv.org/abs/2205.12580},
  author = {Rogenmoser, Michael and Wistoff, Nils and Vogel, Pirmin and Gürkaynak, Frank and Benini, Luca},
  keywords = {Distributed, Parallel, and Cluster Computing (cs.DC), Signal Processing (eess.SP), FOS: Computer and information sciences, FOS: Computer and information sciences, FOS: Electrical engineering, electronic engineering, information engineering, FOS: Electrical engineering, electronic engineering, information engineering},
  title = {On-Demand Redundancy Grouping: Selectable Soft-Error Tolerance for a Multicore Cluster},
  publisher = {arXiv},
  year = {2022},
  copyright = {Creative Commons Attribution Share Alike 4.0 International}
}
```

### Maintenance

To re-generate regfile, run following command in the root directory of this repo.
```bash
make gen_ODRG
```
This will generate the register file SV-code, its corresponding C-code and documentation using lowrisc's reggen tool via the pulp register-interface repository.

## ECC encoders and decoders
ECC encoders and decoders are imported using lowRISC's `vendor.py` script. To re-import and re-generate the `prim_secded_` modules run
```bash
make gen_ECC
```

## ECC wrapper for SRAM
`ecc_sram_wrap.sv` is a wrapper for the tc_sram tech_cell to add ecc in a customizable fashion. It interfaces a modified `TCDM_BANK_MEM_BUS.Slave` defined in pulp_soc with the memory, implementing a load-and-store architecture for writes where not the full word is written. As this requires an additional cycle, a gnt signal is exposed, delaying the subsequent transaction if necessary.

## ECC scrubber
`ecc_scrubber.sv` is a scrubber unit to attach to an ecc-protected memory bank. When triggered, read the next address to detect if a fault has occurred, correcting it if required and logging the number of corrections. It will always give way to other memory accesses and stall to avoid increased latency.

## ECC translators for data bus interfaces
The `BUS_enc_dec` encoders and decoders add or remove ECC to the parametrized `XBAR_TCDM_BUS`, `XBAR_PE_BUS`, and `XBAR_DEMUX_BUS`, defined in [pulp_interfaces.sv](https://github.com/micprog/pulp_soc/blob/ibex_update/rtl/components/pulp_interfaces.sv), as well as [`AXI_BUS`](https://github.com/pulp-platform/axi).

The `DropECC` parameter allows for a faster signal along the decode data path, not correcting the errors but still calculating if an error exists.

## Triple Modular Redundancy majority voters
The `TMR_voter`s are Triple Modular Redundancy majority voters, based on research indicated in the corresponding files. To detect the failing module, additional signals are implemented in higher-level modules.

## Testing
To run tests, execute the following command:
```bash
./run_tests.sh
```

A bender installation >=v0.22 is required.
