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

# Test Settings
VSIM_LOGFILE=vsim.log
RunCycles=100

# Remove the old logfile
rm -f $VSIM_LOGFILE

# Compile the Testbench
echo "Compiling Testbench..."
bender script vsim -t test -t rtl > compile.tcl
"$VSIM" -c -do 'source compile.tcl; quit' >> $VSIM_LOGFILE 2>&1
tail -3 $VSIM_LOGFILE
echo ""

echo "Testing TMR protected FFs"

for data_width in 1 2 4 8 16 32 64
do
  echo "Testing Data Width $data_width"
  vsim -voptargs=+acc -GDataWidth=$data_width tb_tmr_reg -do 'log -r /*; do test/tmr_reg_fault_injection.tcl; run -a; quit' >> $VSIM_LOGFILE 2>&1

  echo "DataWidth=$data_width:"
  tail -3 $VSIM_LOGFILE
  echo ""
done

echo "Finished TMR Reg testing"
