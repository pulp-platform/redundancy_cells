// Copyright 2022 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Luca Rufer <lrufer@student.ethz.ch>


/// This module joins the instruction addresses of multiple sources. If they
/// match, then the requested instruction address is given to the output
/// (normally the ICache). The instruction data is distributed to all sources,
/// along with the ready signals 'ready_o' that indicate if the instruction
/// data is valid.
///
/// This module assumes that the source is always ready to accept the
/// instruction data and thus there is no ready signal for the instuction data.
/// The valid signal for the instruction data is combined with the ready signal
/// for the instruction address.
///
/// All instruction requests are processed if the addresses from the sources
/// match. If the addresses don't match while the valid signals are active, or
/// the valid signals of the sources don't agree, an error signal is generated.
/// This module dones not offer a way to repreat the request. The request
/// can simply be repeated by applying the same address in the next cycle.

module dmr_instr_join_fork #(
  parameter type addr_t      = logic,
  parameter type data_t      = logic,
  parameter int  NUM_IN      = 2
)(
  input  logic clk_i,
  input  logic rst_ni,
  output logic error_o,
  input  logic error_ext_i,
  // address source
  input  logic  [NUM_IN-1:0] valid_i,
  output logic  [NUM_IN-1:0] ready_o,
  input  addr_t [NUM_IN-1:0] addr_i,
  output data_t [NUM_IN-1:0] data_o,
  // data source
  output logic  valid_o,
  input  logic  ready_i,
  output addr_t addr_o,
  input  data_t data_i
);

  addr_t addr_q;
  logic valid_q;

  assign addr_o  = (error_o | error_ext_i) ?  addr_q :  addr_i[0];
  assign valid_o = (error_o | error_ext_i) ? valid_q : valid_i[0];
  assign data_o  = {NUM_IN{data_i}};
  assign ready_o = {NUM_IN{ready_i}};

  always_comb begin
    error_o = 1'b0;
    // output comparator logic
    for(int i = 1; i < NUM_IN; i++) begin
      if(addr_i[i] != addr_i[i-1] || valid_i[i] != valid_i[i-1]) begin
        error_o = 1'b1;
      end
    end
  end

  // addr store update
  always_ff @(posedge (clk_i) or negedge (rst_ni)) begin
    if (!rst_ni) begin
      addr_q <= '0;
      valid_q <= '0;
    end else begin
      addr_q <= addr_o;
      valid_q <= valid_o;
    end
  end

endmodule
