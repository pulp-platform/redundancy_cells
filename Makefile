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

BENDER ?= ./bender
REG_PATH = $(shell $(BENDER) path register_interface)
# use if you need to hardcode location of regtool
# REG_PATH = ../register_interface
REG_TOOL = $(REG_PATH)/vendor/lowrisc_opentitan/util/regtool.py

HJSON_ODRG = rtl/ODRG_unit/ODRG_unit.hjson
HJSON_TCLS = rtl/pulpissimo_tcls/TCLS_unit.hjson
HJSON_HMR = rtl/HMR/HMR_regs.hjson
HJSON_ECC = rtl/ecc_wrap/ecc_sram_wrapper.hjson

TARGET_DIR_ODRG = rtl/ODRG_unit
TARGET_DIR_TCLS = rtl/pulpissimo_tcls
TARGET_DIR_HMR = rtl/HMR
TARGET_DIR_ECC = rtl/ecc_wrap

.PHONY: gen_ODRG gen_TCLS gen_ecc_registers gen_ECC
gen_ODRG:
	python $(REG_TOOL) $(HJSON_ODRG) -t $(TARGET_DIR_ODRG) -r
	python $(REG_TOOL) $(HJSON_ODRG) -d > $(TARGET_DIR_ODRG)/doc.html
	python $(REG_TOOL) $(HJSON_ODRG) -D > $(TARGET_DIR_ODRG)/ODRG.h
	python $(REG_TOOL) $(HJSON_ODRG) --doc > $(TARGET_DIR_ODRG)/doc.md

gen_TCLS:
	python $(REG_TOOL) $(HJSON_TCLS) -t $(TARGET_DIR_TCLS) -r
	python $(REG_TOOL) $(HJSON_TCLS) -d > $(TARGET_DIR_TCLS)/doc.html
	python $(REG_TOOL) $(HJSON_TCLS) -D > $(TARGET_DIR_TCLS)/TCLS.h
	python $(REG_TOOL) $(HJSON_TCLS) --doc > $(TARGET_DIR_TCLS)/doc.md

gen_HMR:
	python $(REG_TOOL) $(HJSON_HMR) -t $(TARGET_DIR_HMR) -r
	python $(REG_TOOL) $(HJSON_HMR) -d > $(TARGET_DIR_HMR)/doc.html
	python $(REG_TOOL) $(HJSON_HMR) -D > $(TARGET_DIR_HMR)/HMR.h
	python $(REG_TOOL) $(HJSON_HMR) --doc > $(TARGET_DIR_HMR)/doc.md

gen_ecc_registers:
	python $(REG_TOOL) $(HJSON_ECC) -t $(TARGET_DIR_ECC) -r
	python $(REG_TOOL) $(HJSON_ECC) -d > $(TARGET_DIR_ECC)/doc.html
	python $(REG_TOOL) $(HJSON_ECC) -D > $(TARGET_DIR_ECC)/ECC.h
	python $(REG_TOOL) $(HJSON_ECC) --doc > $(TARGET_DIR_ECC)/doc.md

gen_ECC:
	./util/vendor.py util/lowrisc_opentitan.vendor.hjson
	cd util/lowrisc_opentitan && ./util/design/secded_gen.py --no_fpv --outdir ../../rtl/lowrisc_ecc

bender:
ifeq (,$(wildcard ./bender))
	curl --proto '=https' --tlsv1.2 -sSf https://pulp-platform.github.io/bender/init \
		| bash -s -- 0.26.1
	touch bender
endif

.PHONY: bender-rm
bender-rm:
	rm -f bender
