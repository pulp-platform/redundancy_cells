
set MaxDataWidth [examine -radix dec sim:/tb_ecc_reg_multi/MaxDataWidth]

when { sim:/tb_ecc_reg_multi/gen_dut[1]/i_dut/clk == 1'b0 } {
  for {set dw 1} {$dw <= $MaxDataWidth} {incr dw} {
    set val [examine sim:/tb_ecc_reg_multi/gen_dut[$dw]/i_dut/i_dut/data_q]
    set inject_val [examine sim:/tb_ecc_reg_multi/gen_dut[$dw]/i_dut/inject_val]
    force -deposit sim:/tb_ecc_reg_multi/gen_dut[$dw]/i_dut/i_dut/data_q $inject_val
    #echo "Flipped $val to $inject_val"
  }
}
