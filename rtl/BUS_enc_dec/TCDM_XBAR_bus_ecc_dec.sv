// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// 
// Removes SECDED ECC from TCDM_XBAR_BUS

module TCDM_XBAR_bus_ecc_dec #(
  localparam int unsigned DataWidth = 32 // Currently will only work for 32
) (
  XBAR_TCDM_BUS.Slave  bus_in,     // DATA_WIDTH=39
  XBAR_TCDM_BUS.Master bus_out,    // DATA_WIDTH=32
  output logic [  6:0] syndrome_o,
  output logic [  1:0] err_o
);
`ifndef TARGET_SYNTHESIS
  if (bus_in.DATA_WIDTH != 39) $fatal("Ensure bus_in DATA_WIDTH");
  if (bus_out.DATA_WIDTH != 32) $fatal("Ensure bus_out DATA_WIDTH");
`endif

  assign bus_out.req    = bus_in.req;
  assign bus_out.add    = bus_in.add;
  assign bus_out.wen    = bus_in.wen;
  assign bus_out.be     = bus_in.be;

  assign bus_in.gnt     = bus_out.gnt;
  assign bus_in.r_opc   = bus_out.r_opc;
  assign bus_in.r_valid = bus_out.r_valid;

  prim_secded_39_32_enc ecc_encode (
    .in  ( bus_out.r_rdata ),
    .out ( bus_in.r_rdata  )
  );

  prim_secded_39_32_dec ecc_decode (
    .in         ( bus_in.wdata  ),
    .d_o        ( bus_out.wdata ),
    .syndrome_o ( syndrome_o    ),
    .err_o      ( err_o         )
  );

endmodule

