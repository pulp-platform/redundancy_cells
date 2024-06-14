#!/usr/bin/env bash
# Copyright (c) 2021 ETH Zurich, University of Bologna
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
# 
# Testing script for redundancy cells

set -e

[ ! -z "$VSIM" ] || VSIM=vsim

VSIM_LOGFILE=vsim.log

bender script vsim -t test -t rtl --vlog-arg="-svinputport=compat" -t deprecated > compile.tcl

$VSIM -c -do 'source compile.tcl; quit' > vcom.log

rm -f $VSIM_LOGFILE

call_vsim() {
  if [ $1 == tb_ecc_sram ]; then
    echo "source test/ecc_sram_fault_injection.tcl; run -all" | $VSIM "$@" >> $VSIM_LOGFILE 2>&1
  else
    echo "run -all" | $VSIM "$@" >> $VSIM_LOGFILE 2>&1
  fi
  echo "  --> $@"
  tail -7 $VSIM_LOGFILE
  echo ""
  # grep "Errors: 0," vsim.log
}

call_vsim tb_tmr_voter
call_vsim tb_tmr_voter_fail
call_vsim tb_tmr_voter_detect
call_vsim tb_tmr_word_voter
call_vsim tb_bitwise_tmr_voter
call_vsim tb_bitwise_tmr_voter_fail
call_vsim tb_ecc_sram -voptargs="+acc=nr"
call_vsim -GDataWidth=8 tb_ecc_secded
call_vsim -GDataWidth=16 tb_ecc_secded
call_vsim -GDataWidth=32 tb_ecc_secded
call_vsim -GDataWidth=64 tb_ecc_secded
call_vsim tb_ecc_scrubber
call_vsim tb_voter_macros

call_vsim tb_retry
call_vsim tb_retry_inorder

for redundancy in 0 1; do
  call_vsim tb_redundancy_controller -GInternalRedundancy=$redundancy
  
  for early_valid in 0 1; do
    call_vsim tb_time_tmr -GEarlyValidEnable=$early_valid -GInternalRedundancy=$redundancy
    call_vsim tb_time_tmr_lock -GEarlyValidEnable=$early_valid -GInternalRedundancy=$redundancy
  done

  call_vsim tb_time_dmr -GInternalRedundancy=$redundancy
  call_vsim tb_time_dmr_retry -GInternalRedundancy=$redundancy
  call_vsim tb_time_dmr_retry_lock -voptargs="+acc" -GInternalRedundancy=$redundancy
done

for num in 1 4 7; do
  call_vsim tb_rr_arb_tree_lock -GNumInp=$num -coverage -voptargs="+acc +cover=bcesfx" -suppress vsim-3009
done
