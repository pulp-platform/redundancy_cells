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
MAX_DATA_WIDTH=502

rm -f $VSIM_LOGFILE

bender script vsim -t test -t rtl > compile.tcl

echo "Compiling Testbench..."
"$VSIM" -c -do 'source compile.tcl; quit' >> $VSIM_LOGFILE 2>&1
tail -3 $VSIM_LOGFILE
echo ""

echo "Testing Encode and Decode"
for ECC_Select in "0 0 NoECC" "0 1 SED-Parity" "1 0 SEC-Hamming" "0 2 DED-Hamming" "1 2 SECDED-Hsiao" "0 3 TED-Hsiao"
do
  ECC_Params=( $ECC_Select );
  NumErrorCorrect=${ECC_Params[0]};
  NumErrorDetect=${ECC_Params[1]};
  CodeName=${ECC_Params[2]}

  echo "Testing Code: $CodeName"
  echo "run -all; quit" | vsim -voptargs=+acc -c -GMaxDataWidth=$MAX_DATA_WIDTH -GNumErrorCorrect=$NumErrorCorrect -GNumErrorDetect=$NumErrorDetect tb_ecc_enc_cor_multi >> $VSIM_LOGFILE 2>&1
  tail -4 $VSIM_LOGFILE
  echo ""
done

echo "Testing ECC protected FFs"
for SelfCorrect in 0 1
do
  for Encode in 0 1
  do
    for Decode in 0 1
    do
      for ECC_Select in "0 0 NoECC" "0 1 SED-Parity" "1 0 SEC-Hamming" "0 2 DED-Hamming" "1 2 SECDED-Hsiao" "0 3 TED-Hsiao"
      do
        ECC_Params=( $ECC_Select );
        NumErrorCorrect=${ECC_Params[0]};
        NumErrorDetect=${ECC_Params[1]};
        CodeName=${ECC_Params[2]}

        echo "Testing Code: $CodeName, Decode=$Decode, Encode=$Encode, SelfCorrect=$SelfCorrect"
        vsim -c -voptargs=+acc -GMaxDataWidth=$MAX_DATA_WIDTH -GNumErrorCorrect=$NumErrorCorrect -GNumErrorDetect=$NumErrorDetect -GDecode=$Decode -GEncode=$Encode -GSelfCorrect=$SelfCorrect tb_ecc_reg_multi -do test_run.tcl >> $VSIM_LOGFILE 2>&1

        echo "DataWidth=$DataWidth, Code=$CodeName, "
        tail -4 $VSIM_LOGFILE
        echo ""
      done
    done
  done
done

echo "Finished ECC testing"
