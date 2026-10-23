// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Kai Berszin <kberszin@iis.ee.ethz.ch>
//
// Checks rel_edge_detect against a reference edge detector, with and without
// an upset in one copy of the history.

module tb_rel_edge_detect;

  localparam int unsigned Width = 4;

  logic clk = 1'b0, rst_n = 1'b0;
  logic [Width-1:0] d, d_q, re, fe;
  logic fault;
  int unsigned errors = 0, checks = 0;

  always #5ns clk = ~clk;

  rel_edge_detect #(
    .Width ( Width )
  ) i_dut (
    .clk_i   ( clk   ),
    .rst_ni  ( rst_n ),
    .d_i     ( d     ),
    .re_o    ( re    ),
    .fe_o    ( fe    ),
    .fault_o ( fault )
  );

  // Reference without redundancy
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) d_q <= '0;
    else        d_q <= d;

  task automatic chk(input string name, input logic [Width-1:0] got, exp);
    checks++;
    if (got !== exp) begin
      $display("[TB] ERROR %s: got %b, expected %b", name, got, exp);
      errors++;
    end
  endtask

  // Compare now, d is stable
  task automatic compare_now(input logic exp_fault);
    chk("re", re, d & ~d_q);
    chk("fe", fe, ~d & d_q);
    chk("fault", fault, exp_fault);
  endtask

  // Compare just before the next rising edge
  task automatic compare(input logic exp_fault);
    @(negedge clk);
    #4ns;
    compare_now(exp_fault);
  endtask

  // Flip one copy of the history for the rest of the cycle; the flop keeps the
  // forced value after the release until the next clock edge
  logic [Width-1:0] upset_val;
  task automatic upset(input int unsigned copy, input logic [Width-1:0] mask);
    @(negedge clk);
    upset_val = i_dut.hist_q[copy] ^ mask;
    case (copy)
      0: begin force i_dut.hist_q[0] = upset_val; #1ns release i_dut.hist_q[0]; end
      1: begin force i_dut.hist_q[1] = upset_val; #1ns release i_dut.hist_q[1]; end
      2: begin force i_dut.hist_q[2] = upset_val; #1ns release i_dut.hist_q[2]; end
    endcase
  endtask

  initial begin
    d = '0;
    repeat (3) @(posedge clk);
    rst_n = 1'b1;

    // Random input, no upsets: identical to the reference, no fault
    repeat (200) begin
      @(posedge clk);
      #1ns d = $urandom();
      compare(1'b0);
    end

    // An upset in one copy, while the input rises, stays low, holds high and
    // falls: no edge is lost or invented, the disagreement is reported for one
    // cycle and gone the cycle after
    for (int unsigned c = 0; c < 3; c++) begin
      for (int unsigned step = 0; step < 4; step++) begin
        logic [Width-1:0] prev, next;
        prev = step inside {2, 3} ? '1 : '0;
        next = step inside {1, 2} ? '1 : '0;
        @(posedge clk);
        #1ns d = prev;
        @(posedge clk);
        #1ns d = next;
        upset(c, 4'b1010);
        #3ns compare_now(1'b1);
        compare(1'b0);
      end
    end

    $display("[TB] %s: %0d checks, %0d errors", errors ? "FAIL" : "PASS", checks, errors);
    $finish;
  end

endmodule
