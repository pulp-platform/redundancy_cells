# Redundancy Cells

This repository contains various modules used to add redundancy.

## Hybrid-Modular Redundancy (HMR)
The `hmr_unit` is designed as a configurable bridge between multiple cores and the system, allowing for independent or lock-step operation, either in DMR or TMR mode. Further recovery mechanisms are implemented, including a SW-based recovery mechanism when in TMR mode with an interrupt being triggered on an error, a rapid recovery mechanism to automatically backup and refill the state with correct values, and in the future a checkpoint-based recovery mechanism.

### Testing
The HMR unit has been integrated in the [PULP cluster](https://github.com/pulp-platform/pulp_cluster/tree/michaero/hmr_merge) and the [Safety Island](https://github.com/pulp-platform/safety_island) in different configurations.

### Citing
If you are using HMR in your academic work you can cite us:
```BibTeX
@article{10.1145/3635161,
author = {Rogenmoser, Michael and Tortorella, Yvan and Rossi, Davide and Conti, Francesco and Benini, Luca},
title = {Hybrid Modular Redundancy: Exploring Modular Redundancy Approaches in RISC-V Multi-Core Computing Clusters for Reliable Processing in Space},
year = {2023},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
issn = {2378-962X},
url = {https://doi.org/10.1145/3635161},
doi = {10.1145/3635161},
abstract = {Space Cyber-Physical Systems (S-CPS) such as spacecraft and satellites strongly rely on the reliability of onboard computers to guarantee the success of their missions. Relying solely on radiation-hardened technologies is extremely expensive, and developing inflexible architectural and microarchitectural modifications to introduce modular redundancy within a system leads to significant area increase and performance degradation. To mitigate the overheads of traditional radiation hardening and modular redundancy approaches, we present a novel Hybrid Modular Redundancy (HMR) approach, a redundancy scheme that features a cluster of RISC-V processors with a flexible on-demand dual-core and triple-core lockstep grouping of computing cores with runtime split-lock capabilities. Further, we propose two recovery approaches, software-based and hardware-based, trading off performance and area overhead. Running at 430MHz, our fault-tolerant cluster achieves up to 1160MOPS on a matrix multiplication benchmark when configured in non-redundant mode and 617 and 414 MOPS in dual and triple mode, respectively. A software-based recovery in triple mode requires 363 clock cycles and occupies 0.612 mm2, representing a 1.3\% area overhead over a non-redundant 12-core RISC-V cluster. As a high-performance alternative, a new hardware-based method provides rapid fault recovery in just 24 clock cycles and occupies 0.660 mm2, namely ∼ 9.4\% area overhead over the baseline non-redundant RISC-V cluster. The cluster is also enhanced with split-lock capabilities to enter one of the available redundant modes with minimum performance loss, allowing execution of a mission-critical portion of code when in independent mode, or a performance section when in a reliability mode, with <400 clock cycles overhead for entry and exit. The proposed system is the first to integrate these functionalities on an open-source RISC-V-based compute device, enabling finely tunable reliability vs. performance trade-offs.},
note = {Just Accepted},
journal = {ACM Trans. Cyber-Phys. Syst.},
month = {nov}
}
```

## On-Demand Redundancy Grouping (ODRG_unit)
The `ODRG_unit` is designed as a configurable bridge between three ibex cores, allowing for independent operation or lock-step operation with majority voting, triggering an interrupt in case a mismatch is detected. It uses lowrisc's reggen tool to generate the required configuration registers.

ODRG has been superceeded by HMR, as HMR integrates all ODRG features. To simplify maintenance, only one is included. If you would like to inspect the code, please check out the tag `v0.5.1`.

### Citing
If you are using ODRG in your academic work you can cite us:
```BibTeX
@INPROCEEDINGS{9912026,
  author={Rogenmoser, Michael and Wistoff, Nils and Vogel, Pirmin and Gürkaynak, Frank and Benini, Luca},
  booktitle={2022 IEEE Computer Society Annual Symposium on VLSI (ISVLSI)}, 
  title={On-Demand Redundancy Grouping: Selectable Soft-Error Tolerance for a Multicore Cluster}, 
  year={2022},
  volume={},
  number={},
  pages={398-401},
  doi={10.1109/ISVLSI54635.2022.00089}
}
```

### Maintenance

To re-generate regfile, run following command in the root directory of this repo.
```bash
make gen_HMR
```
This will generate the register file SV-code, its corresponding C-code and documentation using lowrisc's reggen tool via the pulp register-interface repository.

## ECC encoders and decoders
The hsiao_ecc encoder, decoder, and corrector are based on lowRISC's Hsiao ECC implementation, with an adapted algorithm to deterministically find an appropriate Hsiao matrix. They are implemented in SystemVerilog for efficient parametrization, replacing the generated lowRISC modules.

The lowRISC ECC encoders and decoders are imported using [`bender`'s `vendor` command](https://github.com/pulp-platform/bender#vendor-----copy-files-from-dependencies-that-do-not-support-bender). To re-import and re-generate the `prim_secded_` modules run
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

A [bender](https://github.com/pulp-platform/bender) installation >=v0.27 is required.
