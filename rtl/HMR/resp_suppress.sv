// Copyright 2023 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Suppress the r_valid if set back

module resp_suppress #(
  parameter int unsigned NumOutstanding = 2
) (
  input  logic clk_i,
  input  logic rst_ni,
  
  input  logic setback_i,
  input  logic req_i,
  input  logic gnt_i,
  input  logic r_valid_i,
  output logic r_valid_o
);

  logic [$clog2(NumOutstanding)-1:0] outstanding_d, outstanding_q;
  logic block_d, block_q;

  assign outstanding_d = outstanding_q + (req_i & gnt_i ? 1 : 0) - (r_valid_i ? 1 : 0);

  assign r_valid_o = block_q ? 1'b0 : r_valid_i;

  always_comb begin
    block_d = block_q;
    if (setback_i) begin
      block_d = 1'b1;
    end else if (outstanding_q == 0) begin
      block_d = 1'b0;
    end
  end

  always_ff @( posedge clk_i or negedge rst_ni ) begin : proc_ff
    if (!rst_ni) begin
      outstanding_q <= '0;
      block_q <= '0;
    end else begin
      outstanding_q <= outstanding_d;
      block_q <= block_d;
    end
  end
  
endmodule
