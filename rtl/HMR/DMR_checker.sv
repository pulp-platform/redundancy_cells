/* Copyright 2020 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 * 
 * Dual Modular Redundancy Checker
 * Compares the outputs generated by two IPs and returns error signals
 * in case of mismatch
 * 
 */

module DMR_checker #(
  parameter int unsigned DataWidth = 41,
  parameter int unsigned Pipeline  = 0
)(
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic [DataWidth-1:0] inp_a_i,
  input  logic [DataWidth-1:0] inp_b_i,
  output logic [DataWidth-1:0] check_o,
  output logic                 error_o
);

logic error;
logic [DataWidth-1:0] compare;
logic [DataWidth-1:0] inp_q;

if (Pipeline) begin
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      compare <= '0;
      inp_q   <= '0;
    end else begin
      compare <= inp_a_i ^ inp_b_i;
      inp_q   <= inp_a_i;
    end
  end
end else begin
  assign compare = inp_a_i ^ inp_b_i;
  assign inp_q = inp_a_i;
end
assign error = |compare;
assign check_o = (error) ? '0 : inp_q;
assign error_o = error;

endmodule : DMR_checker
