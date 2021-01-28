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
// Removes SECDED ECC from AXI_BUS

module AXI_bus_ecc_dec #(
  localparam AXI_ADDR_WIDTH = -1, // irrelevant here
  parameter  AXI_DATA_WIDTH = 32, // currently only 32 or 64 bit supported
  localparam AXI_ID_WIDTH   = -1, // irrelevant here
  parameter  AXI_USER_WIDTH = 1, // USER width excluding ECC bits
  localparam NB_ECC_BITS    = (AXI_DATA_WIDTH==32)?7:8   // currently 7bit for DW=32, 8bit for DW=64
) (
  AXI_BUS.Slave                  bus_in,  // data_width=AXI_DW, user_width+=NB_ECC_BITS
  AXI_BUS.Master                 bus_out, // data_width=AXI_DW
  output logic [NB_ECC_BITS-1:0] syndrome_o,
  output logic [1:0]             err_o
);
  // ECC is added to the higher bits of USER signals, calculated from dat bits.
  // No management of failed ECC correction is done here.

  localparam ECC_USER_WIDTH = AXI_USER_WIDTH + NB_ECC_BITS;

  assign bus_out.aw_id     = bus_in.aw_id;
  assign bus_out.aw_addr   = bus_in.aw_addr;
  assign bus_out.aw_len    = bus_in.aw_len;
  assign bus_out.aw_size   = bus_in.aw_size;
  assign bus_out.aw_burst  = bus_in.aw_burst;
  assign bus_out.aw_lock   = bus_in.aw_lock;
  assign bus_out.aw_cache  = bus_in.aw_cache;
  assign bus_out.aw_prot   = bus_in.aw_prot;
  assign bus_out.aw_qos    = bus_in.aw_qos;
  assign bus_out.aw_region = bus_in.aw_region;
  assign bus_out.aw_atop   = bus_in.aw_atop;
  assign bus_out.aw_user   = bus_in.aw_user[AXI_USER_WIDTH-1:0];
  assign bus_out.aw_valid  = bus_in.aw_valid;
  assign bus_in.aw_ready   = bus_out.aw_ready;

  // assign bus_out.w_data    = bus_in.w_data; // remove ecc below
  assign bus_out.w_strb    = bus_in.w_strb;
  assign bus_out.w_last    = bus_in.w_last;
  assign bus_out.w_user    = bus_in.w_user[AXI_USER_WIDTH-1:0]; // remove ecc below
  assign bus_out.w_valid   = bus_in.w_valid;
  assign bus_in.w_ready    = bus_out.w_ready;

  assign bus_in.b_id       =                      bus_out.b_id;
  assign bus_in.b_resp     =                      bus_out.b_resp;
  assign bus_in.b_user     = { {NB_ECC_BITS{1'b0}}, bus_out.b_user };
  assign bus_in.b_valid    =                      bus_out.b_valid;
  assign bus_out.b_ready   =                      bus_in.b_ready;

  assign bus_out.ar_id     = bus_in.ar_id;
  assign bus_out.ar_addr   = bus_in.ar_addr;
  assign bus_out.ar_len    = bus_in.ar_len;
  assign bus_out.ar_size   = bus_in.ar_size;
  assign bus_out.ar_burst  = bus_in.ar_burst;
  assign bus_out.ar_lock   = bus_in.ar_lock;
  assign bus_out.ar_cache  = bus_in.ar_cache;
  assign bus_out.ar_prot   = bus_in.ar_prot;
  assign bus_out.ar_qos    = bus_in.ar_qos;
  assign bus_out.ar_region = bus_in.ar_region;
  assign bus_out.ar_user   = bus_in.ar_user[AXI_USER_WIDTH-1:0];
  assign bus_out.ar_valid  = bus_in.ar_valid;
  assign bus_in.ar_ready   = bus_out.ar_ready;

  assign bus_in.r_id                       = bus_out.r_id;
  // assign bus_in.r_data                     = bus_out.r_data; // add ecc below
  assign bus_in.r_resp                     = bus_out.r_resp;
  assign bus_in.r_last                     = bus_out.r_last;
  assign bus_in.r_user[AXI_USER_WIDTH-1:0] = bus_out.r_user[AXI_USER_WIDTH-1:0]; // add ecc below
  assign bus_in.r_valid                    = bus_out.r_valid;
  assign bus_out.r_ready                   = bus_in.r_ready;

  if (AXI_DATA_WIDTH == 32) begin
    prim_secded_39_32_enc ecc_encode (
      .in  ( bus_out.r_data ),
      .out ( {bus_in.r_user[ECC_USER_WIDTH-1:AXI_USER_WIDTH], bus_in.r_data } )
    );

    prim_secded_39_32_dec ecc_decode (
      .in         ( {bus_in.w_user[ECC_USER_WIDTH-1:AXI_USER_WIDTH], bus_in.w_data } ),
      .d_o        ( bus_out.w_data ),
      .syndrome_o ( syndrome_o     ),
      .err_o      ( err_o          )
    );
  end else if (AXI_DATA_WIDTH == 64) begin
    prim_secded_72_64_enc ecc_encode (
      .in  ( bus_out.r_data ),
      .out ( {bus_in.r_user[ECC_USER_WIDTH-1:AXI_USER_WIDTH], bus_in.r_data } )
    );

    prim_secded_72_64_dec ecc_decode (
      .in         ( {bus_in.w_user[ECC_USER_WIDTH-1:AXI_USER_WIDTH], bus_in.w_data } ),
      .d_o        ( bus_out.w_data ),
      .syndrome_o ( syndrome_o     ),
      .err_o      ( err_o          )
    );
  end else begin
    $fatal(1, "please chose appropriate AXI_DATA_WIDTH or update the code.");
  end

endmodule

