# Redundancy Cells

This repository contains various modules used to add redundancy.

`lowrisc_ecc` folder contains the `secded_gen.py` from lowrisc, along with generated SV ECC encoders and decoders for 8, 16, and 32 bit widths. These were generated using the following command in the folder:
```bash
python secded_gen.py -m 1 -k $WORD_LENGTH --outdir .
```

`ecc_sram_wrap.sv` is a wrapper for the tc_sram tech_cell to add ecc in a customizable fashion. It interfaces a modified `TCDM_BANK_MEM_BUS.Slave` defined in pulp_soc with the memory, implementing a load-and-store architecture for writes where not the full word is written. As this requires an additional cycle, a gnt signal is exposed, delaying the subsequent transaction if necessary.
