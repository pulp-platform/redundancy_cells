# Fault injection file by Michael Rogenmoser
# 
# This script flips a single bit in each memory word at the halfway point in the simulation.
# Not each flip will be tested, as not every bit is read.
# 
# Based in part on:
#   - https://diglib.tugraz.at/download.php?id=576a7490f01c3&location=browse

echo "Bitflip script enabled\n"

when { sim:/tb_ecc_sram/test_halfway == 1'b1 } {
  for {set i 0} {$i < [regsub ".*'h" [examine sim:/tb_ecc_sram/BankSize] "0x"]} {incr i} {
    set indent [expr int(floor(rand()*39))]
    set current_value [examine /tb_ecc_sram/i_dut/i_bank/sram($i)($indent)]
    if {$current_value == "1'h0"} {
      force -deposit /tb_ecc_sram/i_dut/i_bank/sram($i)($indent) 1
    }
    if {$current_value == "1'h1"} {
      force -deposit /tb_ecc_sram/i_dut/i_bank/sram($i)($indent) 0
    }
  }
}
