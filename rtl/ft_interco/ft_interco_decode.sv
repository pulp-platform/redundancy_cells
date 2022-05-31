// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// 
// Decode ft_interco to TCDM bus

module ft_interco_decode #(
  parameter bit          FullImpl  = 0,
  parameter bit          OutECC    = 1,

  parameter type         ft_req_t  = logic,
  parameter type         ft_resp_t = logic,

  parameter int unsigned DataWidth = OutECC ? 39 : 32,
  parameter int unsigned AddrWidth = 32,
  parameter int unsigned BeWidth   = DataWidth/8
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  ft_req_t              ft_req_i,
  output ft_resp_t             ft_resp_o,

  output logic                 tcdm_req_o,
  output logic [AddrWidth-1:0] tcdm_add_o,
  output logic                 tcdm_wen_o,
  output logic [DataWidth-1:0] tcdm_wdata_o,
  output logic [  BeWidth-1:0] tcdm_be_o,
  input  logic                 tcdm_gnt_i,
  input  logic                 tcdm_r_valid_i,
  input  logic [DataWidth-1:0] tcdm_rdata_i,
  input  logic                 tcdm_err_i,

  output [1:0] error_o
);
  let min(a,b) = (a < b) ? a : b;
  if ( FullImpl ) begin
    $fatal("Full encode/decode not implemented yet");
  end

  logic single_wdata_error, wdata_error;
  logic req_match, wen_match, addr_match, be_match;
  assign error_o = {~be_match, ~addr_match, ~wen_match, ~req_match};

  /**
   * REQUEST
   */

  assign tcdm_req_o = ft_req_i.req;
  assign req_match = ft_req_i.req ^ ft_req_i.req_p;

  assign tcdm_add_o = ft_req_i.a.addr;
  localparam AddrWidthParBits = (AddrWidth+7)/8;
  logic [AddrWidthParBits-1:0] addr_match_indiv;
  for (genvar i = 0; i < AddrWidthParBits; i++) begin
    assign addr_match_indiv[i] = ft_req_i.a.addr_p[i] ^ (^ft_req_i.a.addr[min(8*i+7, AddrWidth-1):8*i]);
  end
  assign addr_match = &addr_match_indiv;

  assign tcmd_wen_o = ft_req_i.a.wen;
  assign wen_match = ft_req_i.a.wen ^ ft_req_i.a.wen_p;

  logic [31:0] out_data;
  if ((DataWidth == 32 && !OutECC) || (DataWidth == 39 && OutECC)) begin
    prim_secded_39_32_dec i_wdata_dec (
      .in(ft_req_i.a.wdata_ecc),
      .d_o(out_data),
      .syndrome_o(),
      .err_o({wdata_error, single_wdata_error})
    );
  end else begin
    $fatal("Unsupported data width");
  end

  if ( OutECC ) begin
    assign tcdm_wdata_o = out_data;
  end else begin
    assign tcdm_wdata_o = ft_req_i.a.wdata_ecc;
  end

  localparam int unsigned BeWidthParBits = (BeWidth+7)/8;
  assign tcdm_be_o = ft_req_i.a.be;
  logic [BeWidthParBits-1:0] be_match_indiv;
  for (genvar i = 0; i < BeWidthParBits; i++) begin
    assign be_match_indiv[i] = ft_req_i.a.be_p[i] ^ (^ft_req_i.a.be[min(8*i+7, BeWidth-1):8*i]);
  end
  assign be_match = &be_match_indiv;

  /**
   * RESPONSE
   */

  assign ft_resp_o.gnt = tcdm_gnt_i;
  assign ft_resp_o.gnt_p = ~^tcdm_gnt_i;

  assign ft_resp_o.r_valid = tcdm_r_valid_i;
  assign ft_resp_o.r_valid_p = ~^tcdm_r_valid_i;

  if (OutECC) begin
    assign ft_resp_o.r.data_ecc = tcdm_rdata_i;
  end else begin 
    if (DataWidth == 32) begin
      prim_secded_39_32_enc i_rdata_enc (
        .in(tcdm_rdata_i),
        .out(ft_resp_o.r.data_ecc)
      );
    end else begin
      $fatal("Unsupported data width");
    end
  end

  assign ft_resp_o.r.err = tcdm_err_i;
  assign ft_resp_o.r.err_p = ~^tcdm_err_i;

  assign ft_resp_o.r.user = '0;
  assign ft_resp_o.r.user_p = '1; // Odd parity per byte

  assign ft_resp_o.r.id = '0;
  assign ft_resp_o.r.id_p = '1; // Odd parity per byte

  assign ft_resp_o.r.poison = '0;

endmodule
