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
// Encodes TCDM bus to ft_interco


module ft_interco_encode #(
  parameter bit          FullImpl  = 0,

  parameter type         ft_req_t  = logic,
  parameter type         ft_resp_t = logic,

  parameter int unsigned DataWidth = 32,
  parameter int unsigned AddrWidth = 32,
  parameter int unsigned BeWidth   = DataWidth/8
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  output ft_req_t              ft_req_o,
  input  ft_resp_t             ft_resp_i,

  input  logic                 tcdm_req_i,
  input  logic [AddrWidth-1:0] tcdm_add_i,
  input  logic                 tcdm_wen_i,
  input  logic [DataWidth-1:0] tcdm_wdata_i,
  input  logic [  BeWidth-1:0] tcdm_be_i,
  output logic                 tcdm_gnt_o,
  output logic                 tcdm_r_valid_o,
  output logic [DataWidth-1:0] tcdm_rdata_o,
  output logic                 tcdm_err_o,

  output logic [4:0] error_o
);
  let min(a,b) = (a < b) ? a : b;
  if ( FullImpl ) begin
    $fatal("Full encode/decode not implemented yet");
  end

  logic single_rdata_error, rdata_error;
  logic valid_match, gnt_match, err_match, id_match, user_match;
  assign error_o = {rdata_error, single_rdata_error, ~err_match, ~valid_match, ~gnt_match};

  /**
   * REQUEST
   */

  assign ft_req_o.req = tcdm_req_i;
  assign ft_req_o.req_p = ~^tcdm_req_i; // Odd parity

  localparam AddrWidthParBits = (AddrWidth+7)/8;
  assign ft_req_o.a.addr = tcdm_add_i;
  for (genvar i = 0; i < AddrWidthParBits; i++) begin
    assign ft_req_o.a.addr_p [i] = ~^tcdm_add_i[min(8*i+7, AddrWidth-1):8*i]; // Odd parity per byte
  end

  assign ft_req_o.a.wen = tcdm_wen_i;
  assign ft_req_o.a.wen_p = ~^tcdm_wen_i;

  if (DataWidth == 32) begin
    prim_secded_39_32_enc i_wdata_enc (
      .in(tcdm_wdata_i),
      .out(ft_req_o.a.wdata_ecc)
    );
  end else begin
    $fatal("Unsupported data width");
  end

  localparam int unsigned BeWidthParBits = (BeWidth+7)/8;
  assign ft_req_o.a.be = tcdm_be_i;
  for (genvar i = 0; i < BeWidthParBits; i++) begin
    assign ft_req_o.a.be_p [i] = ~^tcdm_be_i[min(8*i+7, BeWidth-1):8*i]; // Odd parity per byte
  end

  assign ft_req_o.a.user = '0;
  assign ft_req_o.a.user_p = '1; // Odd parity per byte

  assign ft_req_o.a.id = '0;
  assign ft_req_o.a.id_p = '1; // Odd parity per byte

  assign ft_req_o.a.poison = '0;

  /**
   * RESPONSE
   */

  assign tcdm_gnt_o = ft_resp_i.gnt;
  assign gnt_match = ft_resp_i.gnt ^ ft_resp_i.gnt_p;

  assign tcdm_r_valid_o = ft_resp_i.r_valid;
  assign valid_match = ft_resp_i.r_valid ^ ft_resp_i.r_valid_p;

  if (DataWidth == 32) begin
    prim_secded_39_32_dec i_rdata_dec (
      .in(ft_resp_i.r.data_ecc),
      .d_o(tcdm_rdata_o),
      .syndrome_o(),
      .err_o({rdata_error, single_rdata_error})
    );
  end else begin
    $fatal("Unsupported data width");
  end

  assign tcdm_err_o = ft_resp_i.r.err;
  assign err_match = ft_resp_i.r.err ^ ft_resp_i.r.err_p;

endmodule
