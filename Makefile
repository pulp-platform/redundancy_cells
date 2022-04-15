# Copyright 2021 ETH Zurich and University of Bologna
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

SHELL=bash

REG_PATH = ../register_interface
REG_TOOL = $(REG_PATH)/vendor/lowrisc_opentitan/util/regtool.py
HJSON = rtl/ecc_registers/ecc_sram_wrapper.hjson

TARGET_DIR = rtl

# .PHONY: gen_cTCLS
gen_cTCLS:
	python $(REG_TOOL) $(HJSON) -t $(TARGET_DIR) -r
	python $(REG_TOOL) $(HJSON) -d > $(TARGET_DIR)/doc.html
	python $(REG_TOOL) $(HJSON) -D > $(TARGET_DIR)/cTCLS.h
	python $(REG_TOOL) $(HJSON) --doc > $(TARGET_DIR)/doc.md

gen_TCLS:
	python $(REG_TOOL) $(HJSON) -t $(TARGET_DIR) -r
	python $(REG_TOOL) $(HJSON) -d > $(TARGET_DIR)/doc.html
	python $(REG_TOOL) $(HJSON) -D > $(TARGET_DIR)/TCLS.h
	python $(REG_TOOL) $(HJSON) --doc > $(TARGET_DIR)/doc.md

gen_ecc_registers:
	python $(REG_TOOL) $(HJSON) -t $(TARGET_DIR) -r
	python $(REG_TOOL) $(HJSON) -d > $(TARGET_DIR)/doc.html
	python $(REG_TOOL) $(HJSON) -D > $(TARGET_DIR)/ECC.h
	python $(REG_TOOL) $(HJSON) --doc > $(TARGET_DIR)/doc.md

gen_ECC:
	./util/vendor.py util/lowrisc_opentitan.vendor.hjson
	cd util/lowrisc_opentitan && ./util/design/secded_gen.py --no_fpv --outdir ../../rtl/lowrisc_ecc
