// Copyright 2023 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Description: Flipflop with TMR state protection and integrated voter.
//              The FF has two inputs that are to be used in DMR circuits to
//              protect combinatorial logic. The 'dmr_err_o' signal indicates
//              that the input signals don't match. The 'no_load_i' signal
//              is used to prevent the new input from being loaded into the FF.
//              it is advised to connect 'dmr_err_o' ORed with other signals
//              to 'no_load_i' (this is NOT done internally).
//              The 'voter_err_o' signal indicates a voter mismatch. It can
//              be caused by an SEU in a Flip-Flop or an SET in an internal MUX
//              or in the voter.
//              The DMR checking can be disabled by setting 'no_load_i' to 0.
//              However, loading new data when the inputs don't match will cause
//              a voter mismatch one cycle later. Data input 1 takes priority
//              over data input 2.
// Note: This implementation does not feature the LOAD-type FFs, as this can be
//       controlled via the 'no_load_i' signal.
// Note: Special care has to be taken during layout that redundant parts of this
//       module are not optimized away.

// Hint: Use the macros in 'tmr_registers.svh' instead of using this module directly.

`include "common_cells/registers.svh"

module dmr_io_tmr_reg #(
  // Data Settings
  parameter int unsigned DataWidth = 0,
  // FF Settings
  parameter bit HasReset = 1,
  parameter bit AsynchronousReset = 1,
  parameter bit ActiveLowReset = 1
) (
  // Clock and reset
  input  logic                clk_i,
  input  logic                rst_ni,
  // Data Input
  input  logic[DataWidth-1:0] data_1_i,
  input  logic[DataWidth-1:0] data_2_i,
  // Data Output
  output logic[DataWidth-1:0] data_1_o,
  output logic[DataWidth-1:0] data_2_o,
  // Error and Control signals
  output logic                dmr_err_o,
  input  logic                no_load_i,
  output logic                voter_err_o,
  // FF ports
  input  logic[DataWidth-1:0] reset_value_i
);

logic [3*DataWidth-1:0] data_d, data_q, reset_value;

/*****************************
 *  Compare and Select Data  *
 *****************************/

assign dmr_err_o = (data_1_i != data_2_i);

assign data_d = (no_load_i) ? data_q : {3{data_1_i}};

/*****************
 *   Flip-Flop   *
 *****************/

assign reset_value = {3{reset_value_i}};

logic rst;
assign rst = ~rst_ni;

if ( HasReset &&  AsynchronousReset &&  ActiveLowReset) begin
  `FF(data_q, data_d, reset_value, clk_i, rst_ni)
end else if ( HasReset &&  AsynchronousReset && ~ActiveLowReset) begin
  `FFAR(data_q, data_d, reset_value, clk_i, rst)
end else if ( HasReset && ~AsynchronousReset && ~ActiveLowReset) begin
  `FFSR(data_q, data_d, reset_value, clk_i, rst)
end else if ( HasReset && ~AsynchronousReset &&  ActiveLowReset) begin
  `FFSRN(data_q, data_d, reset_value, clk_i, rst_ni)
end else if ( ~HasReset) begin
  `FFNR(data_q, data_d, clk_i)
end

/*******************
 *    Vote Data    *
 *******************/

logic [2:0] voter_err_1, voter_err_2;

// Create two independent voters to prevent common-mode DMR faults
bitwise_TMR_voter #(
  .DataWidth   ( DataWidth                      )
) i_voter_1 (
  .a_i         ( data_q[0*DataWidth+:DataWidth] ),
  .b_i         ( data_q[1*DataWidth+:DataWidth] ),
  .c_i         ( data_q[2*DataWidth+:DataWidth] ),
  .majority_o  ( data_1_o                       ),
  .error_o     (                                ),
  .error_cba_o ( voter_err_1                    )
);

bitwise_TMR_voter #(
  .DataWidth   ( DataWidth                      )
) i_voter_2 (
  .a_i         ( data_q[0*DataWidth+:DataWidth] ),
  .b_i         ( data_q[1*DataWidth+:DataWidth] ),
  .c_i         ( data_q[2*DataWidth+:DataWidth] ),
  .majority_o  ( data_2_o                       ),
  .error_o     (                                ),
  .error_cba_o ( voter_err_2                    )
);

assign voter_err_o = |voter_err_1 | |voter_err_2;

endmodule
