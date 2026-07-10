// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Chaoqun Liang <chaoqun.liang@unibo.it>

module rel_counter #(
    parameter int unsigned WIDTH = 4,
    parameter bit STICKY_OVERFLOW = 1'b0,
    /// Status and control signals are triplicated
    parameter bit          TmrStatus = 1'b0,
    /// DO NOT OVERRIDE
    parameter int unsigned HsWidth = TmrStatus ? 3 : 1
)(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic [HsWidth-1:0]    clear_i, // synchronous clear
    input  logic [HsWidth-1:0]    en_i,    // enable the counter
    input  logic [HsWidth-1:0]    load_i,  // load a new value
    input  logic [HsWidth-1:0]    down_i,  // downcount, default is up
    input  logic [WIDTH-1:0]      d_i,
    output logic [2:0][WIDTH-1:0] q_o,
    output logic [2:0]            overflow_o,
    output logic                  fault_o
);  

    logic [2:0] clear, en, load, down;
    if (TmrStatus) begin : gen_tmr_inputs
        assign clear = clear_i;
        assign en    = en_i;
        assign load  = load_i;
        assign down  = down_i;
    end else begin : gen_broadcast_inputs
        assign clear = {3{clear_i}};
        assign en    = {3{en_i}};
        assign load  = {3{load_i}};
        assign down  = {3{down_i}};
    end

    rel_delta_counter #(
        .WIDTH          (WIDTH),
        .STICKY_OVERFLOW (STICKY_OVERFLOW),
        .TmrStatus      (TmrStatus)
    ) i_counter (
        .clk_i,
        .rst_ni,
        .clear_i(clear),
        .en_i(en),
        .load_i(load),
        .down_i(down),
        .delta_i({3{{{WIDTH-1{1'b0}}, 1'b1}}}),
        .d_i,
        .q_o,
        .overflow_o,
        .fault_o(fault_o)
    );
endmodule