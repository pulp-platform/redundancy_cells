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
  parameter int unsigned NumOutstanding = 2,
  parameter int unsigned AW = 32,
  parameter int unsigned DW = 32
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic            ctrl_setback_i,
  input  logic            bus_hold_i,
  output logic            resp_ok_o,

  input  logic            req_i,
  output logic            gnt_o,
  output logic            r_valid_o,
  input  logic            we_i,
  input  logic [AW  -1:0] addr_i,
  input  logic [DW  -1:0] data_i,
  input  logic [DW/8-1:0] be_i,

  output logic            req_o,
  input  logic            gnt_i,
  input  logic            r_valid_i,
  output logic            we_o,
  output logic [AW  -1:0] addr_o,
  output logic [DW  -1:0] data_o,
  output logic [DW/8-1:0] be_o
);

  logic [$clog2(NumOutstanding)-1:0] outstanding_d, outstanding_q;
  logic block_d, block_q;
  logic latent_req_d, latent_req_q;
  logic latent_req_enforced_d, latent_req_enforced_q;
  logic we_d, we_q;
  logic [AW  -1:0] addr_d, addr_q;
  logic [DW  -1:0] data_d, data_q;
  logic [DW/8-1:0] be_d, be_q;

  // Number of outstanding is current  + additional accepted     - completed
  assign outstanding_d = outstanding_q + (req_o & gnt_i ? 1 : 0) - (r_valid_i ? 1 : 0);

  // The responses are in OK state if there is no outstanding transmission
  assign resp_ok_o = outstanding_q == '0 & ~latent_req_q;

  // Suppress r_valid if there is a latent request signal or we are in block state
  assign r_valid_o = block_q || latent_req_enforced_q ? 1'b0 : r_valid_i;

  // Suppress gnt if there is a latent request signal or we are holding the bus
  assign gnt_o = latent_req_enforced_q || (bus_hold_i & ~latent_req_q) ? 1'b0 : gnt_i;

  // Request is req_i or latent request (protocol compliance), unless bus is being held
  assign req_o = (req_i & ~bus_hold_i) | latent_req_q;
  assign we_o = latent_req_enforced_q ? we_q : we_i;
  assign addr_o = latent_req_enforced_q ? addr_q : addr_i;
  assign data_o = latent_req_enforced_q ? data_q : data_i;
  assign be_o = latent_req_enforced_q ? be_q : be_i;

  assign latent_req_d = req_o & ~gnt_i; // clear latent request if we got the grant

  always_comb begin
    block_d = block_q;
    latent_req_enforced_d = latent_req_enforced_q & ~gnt_i;
    if (latent_req_q && !req_i) begin
      we_d = we_q;
      addr_d = addr_q;
      data_d = data_q;
      be_d = be_q;
    end else begin
      we_d = we_i;
      addr_d = addr_i;
      data_d = data_i;
      be_d = be_i;
    end
    if (ctrl_setback_i) begin
      // block if we got a setback
      block_d = 1'b1;
      // create latent request if requesting on setback call (protocol compliance)
      latent_req_enforced_d = (req_i & ~bus_hold_i) & ~gnt_i;
      we_d = we_i;
      addr_d = addr_i;
      data_d = data_i;
      be_d = be_i;
    end else if (outstanding_q == 0 && !latent_req_q) begin
      block_d = 1'b0;                // Clear block if there are no more outstanding requests
    end
  end

  always_ff @( posedge clk_i or negedge rst_ni ) begin : proc_ff
    if (!rst_ni) begin
      outstanding_q <= '0;
      block_q <= '0;
      latent_req_q <= '0;
      latent_req_enforced_q <= '0;
      we_q <= '0;
      addr_q <= '0;
      data_q <= '0;
      be_q <= '0;
    end else begin
      outstanding_q <= outstanding_d;
      block_q <= block_d;
      latent_req_q <= latent_req_d;
      latent_req_enforced_q <= latent_req_enforced_d;
      we_q <= we_d;
      addr_q <= addr_d;
      data_q <= data_d;
      be_q <= be_d;
    end
  end

endmodule
