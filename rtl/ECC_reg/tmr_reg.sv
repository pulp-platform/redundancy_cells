// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Description: Flipflop with TMR protection and integrated voter
// Hint: Use the macros in 'tmr_registers.svh' instead of using this module directly.

`include "common_cells/registers.svh"

module tmr_reg #(
  // Data Settings
  parameter int unsigned DataWidth = 0,
  // FF Settings
  parameter bit HasReset = 1,
  parameter bit AsynchronousReset = 1,
  parameter bit ActiveLowReset = 1,
  parameter bit HasLoad = 0
) (
  // Clock and reset
  input  logic                clk_i,
  input  logic                rst_ni,
  // Data
  input  logic[DataWidth-1:0] data_i,
  output logic[DataWidth-1:0] data_o,
  output logic                err_o,
  // FF ports
  input  logic[DataWidth-1:0] reset_value_i,
  input  logic                load_en_i
);

logic [3*DataWidth-1:0] data_d, data_q, reset_value;

/*******************
 *   Encode Data   *
 *******************/

assign data_d      = {3{data_i}};
assign reset_value = {3{reset_value_i}};

/*****************
 *   Flip-Flop   *
 *****************/

logic rst;
assign rst = ~rst_ni;

if ( HasReset &&  AsynchronousReset &&  ActiveLowReset && ~HasLoad) begin
  `FF(data_q, data_d, reset_value, clk_i, rst_ni)
end else if ( HasReset &&  AsynchronousReset && ~ActiveLowReset && ~HasLoad) begin
  `FFAR(data_q, data_d, reset_value, clk_i, rst)
end else if ( HasReset && ~AsynchronousReset && ~ActiveLowReset && ~HasLoad) begin
  `FFSR(data_q, data_d, reset_value, clk_i, rst)
end else if ( HasReset && ~AsynchronousReset &&  ActiveLowReset && ~HasLoad) begin
  `FFSRN(data_q, data_d, reset_value, clk_i, rst_ni)
end else if ( ~HasReset && ~HasLoad) begin
  `FFNR(data_q, data_d, clk_i)
end else if ( HasReset &&  AsynchronousReset &&  ActiveLowReset && HasLoad) begin
  `FFL(data_q, data_d, load_en_i, reset_value, clk_i, rst_ni)
end else if ( HasReset &&  AsynchronousReset && ~ActiveLowReset && HasLoad) begin
  `FFLAR(data_q, data_d, load_en_i, reset_value, clk_i, rst)
end else if ( HasReset && ~AsynchronousReset && ~ActiveLowReset && HasLoad) begin
  `FFLSR(data_q, data_d, load_en_i, reset_value, clk_i, rst)
end else if ( HasReset && ~AsynchronousReset &&  ActiveLowReset && HasLoad) begin
  `FFLSRN(data_q, data_d, load_en_i, reset_value, clk_i, rst_ni)
end else if ( ~HasReset && HasLoad) begin
  `FFLNR(data_q, data_d, load_en_i, clk_i)
end

/*******************
 *   Decode Data   *
 *******************/

logic [DataWidth-1:0] data_a, data_b, data_c, diff_ab, diff_bc, sel;

assign data_a = data_q[0*DataWidth+:DataWidth];
assign data_b = data_q[1*DataWidth+:DataWidth];
assign data_c = data_q[2*DataWidth+:DataWidth];

assign diff_ab = data_a ^ data_b;
assign diff_bc = data_b ^ data_c;

assign sel = diff_ab & ~diff_bc;

for (genvar i = 0; i < DataWidth; i++) begin : sel_out
  assign data_o[i] = sel[i] ? data_c[i] : data_a[i];
end

assign err_o = |(diff_ab | diff_bc);

endmodule
