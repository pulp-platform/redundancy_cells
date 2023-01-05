# Helper script for the testbench:
# The Testbench calcutales the value it wants to inject (inject_val), this script
# reads the value and injects in on the falling clock edge.

when { sim:/tb_tmr_reg/clk == 1'b0 } {
    set val [examine sim:/tb_tmr_reg/i_dut/data_q]
    set inject_val [examine sim:/tb_tmr_reg/inject_val]
    force -deposit sim:/tb_tmr_reg/i_dut/data_q $inject_val
    #echo "Flipped $val to $inject_val"
}
