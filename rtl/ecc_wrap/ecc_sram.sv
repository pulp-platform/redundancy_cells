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
// ECC-protected SRAM, with enconding and decoding (if needed), bytewise access, and scrubbing

module ecc_sram #(
  parameter  int unsigned NumWords         = 256,
  parameter  int unsigned UnprotectedWidth = 32,
  parameter  int unsigned ProtectedWidth   = UnprotectedWidth + hsiao_ecc_pkg::min_ecc(UnprotectedWidth),
  parameter  bit          InputECC         = 0, // 0: no ECC on input
                                                // 1: SECDED on input
  parameter  int unsigned NumRMWCuts       = 0, // Number of cuts in the read-modify-write path,
                                                // more than 1 gives no timing benefit
  parameter               SimInit          = "random", // ("zeros", "ones", "random", "none")
  parameter  int unsigned ByteWidth        = 8,
  parameter  int unsigned BankAccessLatency = 1,
  // Set params
  localparam int unsigned DataInWidth      = InputECC ? ProtectedWidth : UnprotectedWidth,
  localparam int unsigned ByteEnWidth      = UnprotectedWidth/ByteWidth,
  localparam int unsigned BankAddrWidth    = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     scrub_trigger_i, // Set to 1'b0 to disable scrubber
  output logic                     scrubber_fix_o,
  output logic                     scrub_uncorrectable_o,

  input  logic [  DataInWidth-1:0] wdata_i,
  input  logic [BankAddrWidth-1:0] addr_i,
  input  logic                     req_i,
  input  logic                     we_i,
  input  logic [  ByteEnWidth-1:0] be_i,
  output logic [  DataInWidth-1:0] rdata_o,
  output logic                     gnt_o,

  output logic                     single_error_o,
  output logic                     multi_error_o
);

  logic                      internal_we;
  logic                      bank_req;
  logic                      bank_we;
  logic [ BankAddrWidth-1:0] bank_addr;
  logic [ProtectedWidth-1:0] bank_wdata;
  logic [ProtectedWidth-1:0] bank_rdata;

  logic                      bank_scrub_req;
  logic                      bank_scrub_we;
  logic [ BankAddrWidth-1:0] bank_scrub_addr;
  logic [ProtectedWidth-1:0] bank_scrub_wdata;
  logic [ProtectedWidth-1:0] bank_scrub_rdata;

  typedef enum logic { NORMAL, READ_MODIFY_WRITE } store_state_e;
  store_state_e store_state_d, store_state_q;

  localparam int unsigned RMWWaitCycles =
      (BankAccessLatency > 0 ? BankAccessLatency - 1 : 0) + NumRMWCuts;
  typedef logic [cf_math_pkg::idx_width(RMWWaitCycles + 1)-1:0] rmw_count_t;
  rmw_count_t rmw_count_d, rmw_count_q;

  logic [  DataInWidth-1:0] input_buffer_d, input_buffer_q;
  logic [BankAddrWidth-1:0] addr_buffer_d,  addr_buffer_q;
  logic [  ByteEnWidth-1:0] be_buffer_d,    be_buffer_q;

  logic [UnprotectedWidth-1:0] be_selector;
  for (genvar i = 0; i < ByteEnWidth; i++) begin : gen_be_sel
    assign be_selector [i*ByteWidth +: ByteWidth] = {ByteWidth{be_buffer_q[i]}};
  end

  // Read-modify-write cut, breaking the long single-cycle path
  // SRAM read -> decode -> merge -> encode -> SRAM write.
  logic [ProtectedWidth-1:0] rmw_buffer_end;
  shift_reg #(
    .dtype(logic[ProtectedWidth-1:0]),
    .Depth(NumRMWCuts)
  ) i_rmw_buffer (
    .clk_i,
    .rst_ni,
    .d_i   (bank_rdata),
    .d_o   (rmw_buffer_end)
  );

  // Read-modify-write operands, plain data in the write-back cycle:
  //   rmw_old    stored word, read and decoded
  //   rmw_new    write data, decoded if InputECC == 1
  //   rmw_merged rmw_new on the enabled bytes, rmw_old elsewhere, to be encoded and
  //              written back
  // An uncorrectable error in rmw_old or rmw_new thus ends up stored with valid ECC. Only
  // multi_error_o reports it.
  logic [UnprotectedWidth-1:0] rmw_old, rmw_new, rmw_merged;
  // ECC errors seen by plain reads and by the read of a RMW
  logic [1:0] rd_error, rmw_error;

  if ( !InputECC ) begin : gen_no_ecc_input
    // Loads  -> loads full data
    // Stores ->
    //   If be_i == '1: adds ECC and stores directly
    //   If be_i != '1: loads stored and buffers input (responds success to store command)
    //                  re-calculates ECC and stores correctly

    logic [UnprotectedWidth-1:0] to_store;
    logic [UnprotectedWidth-1:0] loaded;

    hsiao_ecc_dec #(
      .DataWidth (UnprotectedWidth),
      .ProtWidth (ProtectedWidth - UnprotectedWidth)
    ) ecc_decode (
      .in        ( bank_rdata ),
      .out       ( loaded ),
      .syndrome_o(),
      .err_o     ( rd_error )
    );

    assign rdata_o = loaded;

    if (NumRMWCuts == 0) begin : gen_rmw_shared_decode
      // Without a cut the RMW reads the bank in its write-back cycle and shares the read decoder.
      assign rmw_old   = loaded;
      assign rmw_error = rd_error;
    end else begin : gen_rmw_decode
      // With a cut the RMW has its own decoder behind the cut. Sharing the read decoder would
      // need a mux on its input, which leaves a combinational path from the SRAM output through
      // the decoder and the merge back into the SRAM. That path is false, the two mux legs are
      // used in different states, but timing analysis still reports it and the cut has no effect.
      hsiao_ecc_dec #(
        .DataWidth (UnprotectedWidth),
        .ProtWidth (ProtectedWidth - UnprotectedWidth)
      ) rmw_decode (
        .in        ( rmw_buffer_end ),
        .out       ( rmw_old ),
        .syndrome_o(),
        .err_o     ( rmw_error )
      );
    end

    assign rmw_new = input_buffer_q;

    assign to_store = store_state_q == NORMAL ? wdata_i : rmw_merged;

    hsiao_ecc_enc #(
      .DataWidth (UnprotectedWidth),
      .ProtWidth (ProtectedWidth - UnprotectedWidth)
    ) ecc_encode (
      .in  ( to_store   ),
      .out ( bank_wdata )
    );

  end else begin : gen_ecc_input
    // Plain reads and full writes pass the codeword through unchecked, the requester and the
    // interconnect protect it end to end. Only a RMW decodes, so only a RMW reports ECC errors.

    logic [ProtectedWidth-1:0] lns_wdata;
    logic [1:0] ld_error, st_error;

    assign rdata_o  = bank_rdata;
    assign rd_error = '0;

    hsiao_ecc_dec #(
      .DataWidth (UnprotectedWidth),
      .ProtWidth (ProtectedWidth - UnprotectedWidth)
    ) ld_decode (
      .in        ( rmw_buffer_end ),
      .out       ( rmw_old ),
      .syndrome_o(),
      .err_o     ( ld_error )
    );

    hsiao_ecc_dec #(
      .DataWidth (UnprotectedWidth),
      .ProtWidth (ProtectedWidth - UnprotectedWidth)
    ) st_decode (
      .in        ( input_buffer_q ),
      .out       ( rmw_new ),
      .syndrome_o(),
      .err_o     ( st_error )
    );

    assign rmw_error = ld_error | st_error;

    hsiao_ecc_enc #(
      .DataWidth (UnprotectedWidth),
      .ProtWidth (ProtectedWidth - UnprotectedWidth)
    ) lns_encode (
      .in  ( rmw_merged ),
      .out ( lns_wdata )
    );

    assign bank_wdata = store_state_q == NORMAL ? wdata_i : lns_wdata;

  end

  assign rmw_merged = (be_selector & rmw_new) | (~be_selector & rmw_old);

  // It might happen (especially with HWPEs driving part of the byte enable to zero) that sometimes
  // a write happens with be_i = '0 but with a non-zero data on the wdata_i bus. In this particular
  // case, the following FSM will still detect a RMW case, leading to either write of unproer data
  // into the TCDM, or to deadlock conditions. We thus introduce a new signal that makes the write
  // enable bus asserted only if the be_i is not all zero during a write operation, and use this to
  // decide if we need to make a RMW or not.
  assign internal_we = we_i & (be_i != '0);

  always_comb begin
    store_state_d  = NORMAL;
    gnt_o          = 1'b1;
    bank_addr      = addr_i;
    bank_we        = internal_we;
    input_buffer_d = wdata_i;
    addr_buffer_d  = addr_i;
    be_buffer_d    = be_i;
    bank_req       = req_i;
    rmw_count_d    = rmw_count_q;
    if (store_state_q == NORMAL) begin
      if (req_i & (be_i != {ByteEnWidth{1'b1}}) & internal_we) begin
        store_state_d = READ_MODIFY_WRITE;
        bank_we       = 1'b0;
        rmw_count_d   = rmw_count_t'(RMWWaitCycles);
      end
    end else begin
      gnt_o           = 1'b0;
      bank_addr       = addr_buffer_q;
      bank_we         = 1'b1;
      input_buffer_d  = input_buffer_q;
      addr_buffer_d   = addr_buffer_q;
      be_buffer_d     = be_buffer_q;
      if (rmw_count_q == '0) begin
        bank_req      = 1'b1;
      end else begin
        bank_req      = 1'b0;
        rmw_count_d   = rmw_count_q - 1;
        store_state_d = READ_MODIFY_WRITE;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_read_modify_write_ff
    if(!rst_ni) begin
      store_state_q  <= NORMAL;
      addr_buffer_q  <= '0;
      input_buffer_q <= '0;
      be_buffer_q    <= '0;
      rmw_count_q    <= '0;
    end else begin
      store_state_q  <= store_state_d;
      addr_buffer_q  <= addr_buffer_d;
      input_buffer_q <= input_buffer_d;
      be_buffer_q    <= be_buffer_d;
      rmw_count_q    <= rmw_count_d;
    end
  end

  // ECC error reporting. A plain read reports when its data leaves the bank, BankAccessLatency
  // cycles after the grant. A RMW reports in its write-back cycle, where the RMW decoders see the
  // word it read. The two never coincide: the bank grants nothing from the grant of a RMW to its
  // write-back, and earlier reads return before the write-back.
  logic plain_read, plain_read_valid, rmw_write;
  assign plain_read = req_i & gnt_o & ~internal_we;
  shift_reg #(
    .dtype(logic),
    .Depth(BankAccessLatency)
  ) i_plain_read_valid (
    .clk_i,
    .rst_ni,
    .d_i   (plain_read),
    .d_o   (plain_read_valid)
  );
  assign rmw_write = (store_state_q == READ_MODIFY_WRITE) && (rmw_count_q == '0);

  assign single_error_o = (rd_error[0] & plain_read_valid) | (rmw_error[0] & rmw_write);
  assign multi_error_o  = (rd_error[1] & plain_read_valid) | (rmw_error[1] & rmw_write);

`ifndef TARGET_SYNTHESIS
  always @(posedge clk_i) begin
    if (single_error_o)
      $display("[ECC] %t - single error detected", $realtime);
    if (multi_error_o)
      $display("[ECC] %t - multi error detected", $realtime);
  end
`endif

  ecc_scrubber #(
    .BankSize       ( NumWords       ),
    .UseExternalECC ( 0              ),
    .DataWidth      ( ProtectedWidth )
  ) i_scrubber (
    .clk_i,
    .rst_ni,

    .scrub_trigger_i ( scrub_trigger_i       ),
    .bit_corrected_o ( scrubber_fix_o        ),
    .uncorrectable_o ( scrub_uncorrectable_o ),

    .intc_req_i      ( bank_req              ),
    .intc_we_i       ( bank_we               ),
    .intc_add_i      ( bank_addr             ),
    .intc_wdata_i    ( bank_wdata            ),
    .intc_rdata_o    ( bank_rdata            ),

    .bank_req_o      ( bank_scrub_req        ),
    .bank_we_o       ( bank_scrub_we         ),
    .bank_add_o      ( bank_scrub_addr       ),
    .bank_wdata_o    ( bank_scrub_wdata      ),
    .bank_rdata_i    ( bank_scrub_rdata      ),

    .ecc_out_o       (),
    .ecc_in_i        ( '0 ),
    .ecc_err_i       ( '0 )
  );

  tc_sram #(
    .NumWords  ( NumWords       ), // Number of Words in data array
    .DataWidth ( ProtectedWidth ), // Data signal width
    .ByteWidth ( ProtectedWidth ), // Width of a data byte
    .NumPorts  ( 1              ), // Number of read and write ports
`ifndef TARGET_SYNTHESIS
    .SimInit   ( SimInit        ),
`endif
    .Latency   ( BankAccessLatency ) // Latency when the read data is available
  ) i_bank (
    .clk_i,                                                   // Clock
    .rst_ni,                                                  // Asynchronous reset active low

    .req_i   ( bank_scrub_req    ), // request
    .we_i    ( bank_scrub_we     ), // write enable
    .addr_i  ( bank_scrub_addr   ), // request address
    .wdata_i ( bank_scrub_wdata  ), // write data
    .be_i    ( '1                ), // write byte enable

    .rdata_o ( bank_scrub_rdata  )  // read data
  );

endmodule
