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
// Edge detector without latency for synchronous inputs: re_o is high in the
// first cycle d_i is high, fe_o in the first cycle it is low again. Unlike
// common_cells edge_detect there is no synchronizer, so the edge appears in
// the same cycle as the input.
//
// The previous value is held in three copies and voted, so an upset in one
// copy neither swallows a real edge nor invents one. Every copy reloads d_i
// each cycle, so a corrupted copy is repaired the cycle after; fault_o
// reports the disagreement for that cycle.

module rel_edge_detect #(
  parameter int unsigned Width      = 1,
  parameter logic [Width-1:0] ResetValue = '0,
  // Triplicate the history; without, an upset can drop or invent one edge
  parameter bit          TmrHistory = 1'b1
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic [Width-1:0] d_i,
  // Rising edge: d_i high, low the cycle before
  output logic [Width-1:0] re_o,
  // Falling edge: d_i low, high the cycle before
  output logic [Width-1:0] fe_o,
  // A copy of the history disagreed with the others (repaired the next cycle)
  output logic             fault_o
);

  localparam int unsigned NumCopies = TmrHistory ? 3 : 1;

  // Identical flops with identical inputs, kept apart so synthesis does not
  // merge the copies
  (* dont_touch = "true" *) logic [Width-1:0] hist_q[NumCopies];
  logic [Width-1:0] hist_v;

  for (genvar c = 0; c < NumCopies; c++) begin : gen_hist
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) hist_q[c] <= ResetValue;
      else         hist_q[c] <= d_i;
    end
  end

  if (TmrHistory) begin : gen_vote
    logic [2:0] err_cba;
    bitwise_TMR_voter #(
      .DataWidth ( Width )
    ) i_voter (
      .a_i         ( hist_q[0] ),
      .b_i         ( hist_q[1] ),
      .c_i         ( hist_q[2] ),
      .majority_o  ( hist_v    ),
      .error_o     (           ),
      .error_cba_o ( err_cba   )
    );
    assign fault_o = |err_cba;
  end else begin : gen_plain
    assign hist_v  = hist_q[0];
    assign fault_o = 1'b0;
  end

  assign re_o = d_i & ~hist_v;
  assign fe_o = ~d_i & hist_v;

endmodule
