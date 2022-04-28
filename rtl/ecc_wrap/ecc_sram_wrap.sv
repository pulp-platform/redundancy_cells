// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// 
// Adapts bus to sram adding ecc bits

module ecc_sram_wrap #(
  parameter  int unsigned BankSize         = 256,
  parameter  bit          InputECC         = 0, // 0: no ECC on input
                                                // 1: SECDED on input
  // Set params
  parameter  int unsigned UnprotectedWidth = 32, // This currently only works for 32bit
  parameter  int unsigned ProtectedWidth   = 39, // This currently only works for 39bit
  localparam int unsigned DataInWidth      = InputECC ? ProtectedWidth : UnprotectedWidth,
  localparam int unsigned BEInWidth        = UnprotectedWidth/8,
  localparam int unsigned BankAddWidth     = $clog2(BankSize)
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,

  input  logic [DataInWidth-1:0] tcdm_wdata_i,
  input  logic [           31:0] tcdm_add_i,
  input  logic                   tcdm_req_i,
  input  logic                   tcdm_wen_i,
  input  logic [  BEInWidth-1:0] tcdm_be_i,
  output logic [DataInWidth-1:0] tcdm_rdata_o,
  output logic                   tcdm_gnt_o,
  output logic                   single_error_o,
  output logic                   multi_error_o
);
  // TODO: - Add memory scrubber

  logic [1:0]                    ecc_error;
  logic                          valid_read_d, valid_read_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_valid_read
    if(~rst_ni) begin
      valid_read_q <= '0;
    end else begin
      valid_read_q <= valid_read_d;
    end
  end

  assign valid_read_d = tcdm_req_i && tcdm_gnt_o && (tcdm_wen_i || (tcdm_be_i != {BEInWidth{1'b1}}));
  assign single_error_o = ecc_error[0] && valid_read_q;
  assign multi_error_o = ecc_error[1] && valid_read_q;

  always_comb begin
    if ((ecc_error[0] && valid_read_q) == 1) $display("[ECC] %t - single error detected", $realtime);
    if ((ecc_error[1] && valid_read_q) == 1) $display("[ECC] %t - multi error detected", $realtime);
  end
 
  

  
  
  logic                      bank_req;
  logic                      bank_we;
  logic [  BankAddWidth-1:0] bank_add;
  logic [ProtectedWidth-1:0] bank_wdata;
  logic                      bank_be;
  logic [ProtectedWidth-1:0] bank_rdata;


  assign bank_be = 1'b1;
  
  
  if ( InputECC == 0 ) begin : ECC_0_ASSIGN
    // Loads  -> loads full data
    // Stores ->
    //   If BE_in == 1111: adds ECC and stores directly
    //   If BE_in != 1111: loads stored and buffers input (responds success to store command)
    //                     re-calculates ECC and stores correctly
    
    logic [DataInWidth-1:0] to_store;
    logic [DataInWidth-1:0] loaded;
    logic [DataInWidth-1:0] be_selector;

    typedef enum logic { NORMAL, LOAD_AND_STORE } store_state_e;
    store_state_e store_state_d, store_state_q;

    logic [ DataInWidth-1:0] input_buffer_d, input_buffer_q;
    logic [BankAddWidth-1:0] add_buffer_d, add_buffer_q;
    logic [   BEInWidth-1:0] be_buffer_d, be_buffer_q;

    prim_secded_39_32_dec ecc_decode (
      .in         ( bank_rdata ),
      .d_o        ( loaded ),
      .syndrome_o (),
      .err_o      (ecc_error)
    );

    prim_secded_39_32_enc ecc_encode (
      .in  ( to_store   ),
      .out ( bank_wdata )
    );

    assign tcdm_rdata_o   = loaded;
    assign add_buffer_d   = tcdm_add_i[BankAddWidth+2-1:2]; // Address input differentiates by byte, memory by word, ensure correct access
    assign input_buffer_d = tcdm_wdata_i;
    assign be_buffer_d    = tcdm_be_i;
    assign be_selector    = {{8{be_buffer_q[3]}},{8{be_buffer_q[2]}},{8{be_buffer_q[1]}},{8{be_buffer_q[0]}}};

    always_comb begin : proc_load_and_store_comb
      store_state_d =  NORMAL;
      tcdm_gnt_o    =  1'b1;
      to_store      =  tcdm_wdata_i;
      bank_we       = ~tcdm_wen_i;
      bank_req      =  tcdm_req_i;
      bank_add      =  tcdm_add_i[BankAddWidth+2-1:2];
      if (store_state_q == NORMAL) begin
        if (tcdm_req_i & (tcdm_be_i != 4'b1111) & ~tcdm_wen_i) begin
          store_state_d = LOAD_AND_STORE;
          bank_we       = 1'b0;
        end
      end else begin
        tcdm_gnt_o = 1'b0;
        to_store   = (be_selector & input_buffer_q) | (~be_selector & loaded);
        bank_we    = 1'b1;
        bank_req   = 1'b1;
        bank_add   = add_buffer_q;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_load_and_store_ff
      if(!rst_ni) begin
        store_state_q  <= NORMAL;
        add_buffer_q   <= '0;
        input_buffer_q <= '0;
        be_buffer_q    <= '0;
      end else begin
        add_buffer_q   <= add_buffer_d;
        store_state_q  <= store_state_d;
        input_buffer_q <= input_buffer_d;
        be_buffer_q    <= be_buffer_d;
      end
    end
  end // ECC_0_ASSIGN
  else if (InputECC == 1 ) begin : ECC_1_ASSIGN
    
    typedef enum logic { NORMAL, LOAD_AND_STORE } store_state_e;
    store_state_e store_state_d, store_state_q;

    logic [ DataInWidth-1:0] input_buffer_d, input_buffer_q;
    logic [BankAddWidth-1:0] add_buffer_d, add_buffer_q;
    logic [   BEInWidth-1:0] be_buffer_d, be_buffer_q;

    logic [  ProtectedWidth-1:0] lns_wdata;
    logic [UnprotectedWidth-1:0] intermediate_data_ld, intermediate_data_st;

    logic [UnprotectedWidth-1:0] be_selector;

    assign tcdm_rdata_o   = bank_rdata;
    assign add_buffer_d   = tcdm_add_i[BankAddWidth+2-1:2];
    assign input_buffer_d = tcdm_wdata_i;
    assign be_buffer_d    = tcdm_be_i;
    assign be_selector    = {{8{be_buffer_q[3]}},{8{be_buffer_q[2]}},{8{be_buffer_q[1]}},{8{be_buffer_q[0]}}};

    prim_secded_39_32_dec ld_decode (
      .in        (bank_rdata),
      .d_o       (intermediate_data_ld),
      .syndrome_o(),
      .err_o     ()
    );

    prim_secded_39_32_dec st_decode (
      .in        (input_buffer_q),
      .d_o       (intermediate_data_st),
      .syndrome_o(),
      .err_o     ()
    );

    prim_secded_39_32_enc lns_encode (
      .in ( (be_selector & intermediate_data_st) | (~be_selector & intermediate_data_ld) ),
      .out(lns_wdata)
    );

    always_comb begin
      store_state_d =  NORMAL;
      tcdm_gnt_o    =  1'b1;
      bank_wdata    =  tcdm_wdata_i;
      bank_we       = ~tcdm_wen_i;
      bank_req      =  tcdm_req_i;
      bank_add      =  tcdm_add_i[BankAddWidth+2-1:2];
      if (store_state_q == NORMAL) begin
        if (tcdm_req_i & (tcdm_be_i != 4'b1111) & ~tcdm_wen_i) begin
          store_state_d = LOAD_AND_STORE;
          bank_we       = 1'b0;
        end
      end else begin // store_state_q == LOAD_AND_STORE
        tcdm_gnt_o  = 1'b0;
        bank_req    = 1'b1;
        bank_we     = 1'b1;
        bank_add    = add_buffer_q;
        bank_wdata  = lns_wdata;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_load_and_store_ff
      if(!rst_ni) begin
        store_state_q  <= NORMAL;
        add_buffer_q   <= '0;
        input_buffer_q <= '0;
        be_buffer_q    <= '0;
      end else begin
        add_buffer_q   <= add_buffer_d;
        store_state_q  <= store_state_d;
        input_buffer_q <= input_buffer_d;
        be_buffer_q    <= be_buffer_d;
      end
    end
  end // ECC_1_ASSIGN

  tc_sram #(
    .NumWords  ( BankSize       ), // Number of Words in data array
    .DataWidth ( ProtectedWidth ), // Data signal width
    .ByteWidth ( ProtectedWidth ), // Width of a data byte
    .NumPorts  ( 1              ), // Number of read and write ports
`ifndef TARGET_SYNTHESIS
    .SimInit   ( "zeros"        ),
`endif
    .Latency   ( 1              ) // Latency when the read data is available
  ) i_bank (
    .clk_i,                  // Clock
    .rst_ni,                 // Asynchronous reset active low

    .req_i   ( bank_req   ), // request
    .we_i    ( bank_we    ), // write enable
    .addr_i  ( bank_add   ), // request address
    .wdata_i ( bank_wdata ), // write data
    .be_i    ( bank_be    ), // write byte enable

    .rdata_o ( bank_rdata )  // read data
  );

endmodule
