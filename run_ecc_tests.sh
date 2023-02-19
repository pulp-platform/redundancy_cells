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
MAX_DATA_WIDTH=502
RunCycles=100
Codes=("0 0 NoECC" "0 1 SED-Parity" "1 0 SEC-Hamming" "0 2 DED-Hamming" "1 2 SECDED-Hsiao" "0 3 TED-Hsiao")
num_codes=${#Codes[@]}

# Remove the old logfile
rm -f $VSIM_LOGFILE

# Compile the Testbench
echo "Compiling Testbench..."
bender script vsim -t test -t rtl > compile.tcl
"$VSIM" -c -do 'source compile.tcl; quit' >> $VSIM_LOGFILE 2>&1
tail -3 $VSIM_LOGFILE
echo ""

# Test Encode and Decode
echo "Testing Encode and Decode"
test_nr=0
num_tests=$num_codes

for i in $(seq 0 $((num_codes-1)))
do
  Code=${Codes[i]}
  ECC_Params=( $Code );
  NumErrorCorrect=${ECC_Params[0]};
  NumErrorDetect=${ECC_Params[1]};
  CodeName=${ECC_Params[2]}

  ((++test_nr))
  echo "Testing Code: $CodeName ($test_nr of $num_tests)"
  echo "run -all; quit" | vsim -voptargs=+acc -c -GMaxDataWidth=$MAX_DATA_WIDTH -GNumErrorCorrect=$NumErrorCorrect -GNumErrorDetect=$NumErrorDetect -GRunCycles=$RunCycles tb_ecc_enc_cor_multi >> $VSIM_LOGFILE 2>&1
  tail -4 $VSIM_LOGFILE
  echo ""
done

echo "Testing ECC protected FFs"
test_nr=0
num_tests=$((2*2*2*num_codes))
for SelfCorrect in 0 1
do
  for Encode in 0 1
  do
    for Decode in 0 1
    do
      for i in $(seq 0 $((num_codes-1)))
      do
        Code=${Codes[i]}
        ECC_Params=( $Code );
        NumErrorCorrect=${ECC_Params[0]};
        NumErrorDetect=${ECC_Params[1]};
        CodeName=${ECC_Params[2]}

        ((++test_nr))
        echo "Testing Code: $CodeName, Decode=$Decode, Encode=$Encode, SelfCorrect=$SelfCorrect ($test_nr of $num_tests)"
        vsim -c -voptargs=+acc -GMaxDataWidth=$MAX_DATA_WIDTH -GNumErrorCorrect=$NumErrorCorrect -GNumErrorDetect=$NumErrorDetect -GDecode=$Decode -GEncode=$Encode -GSelfCorrect=$SelfCorrect -GRunCycles=$RunCycles tb_ecc_reg_multi -do test_run.tcl >> $VSIM_LOGFILE 2>&1

        echo "DataWidth=$DataWidth, Code=$CodeName, "
        tail -4 $VSIM_LOGFILE
        echo ""
      done
    done
  done
done

echo "Finished ECC testing"
