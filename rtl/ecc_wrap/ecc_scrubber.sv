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
// Scrubber for ecc
//   - iteratively steps through memory bank
//   - corrects *only* correctable errors

module ecc_scrubber
  import ariane_pkg::*;
 #(
  parameter int unsigned BankSize       = 256,
  parameter bit          UseExternalECC = 0,
  parameter int unsigned DataWidth      = 39,
  parameter int unsigned ProtWidth      = 7,
  parameter int unsigned AddrWidth      = 8,
  parameter int unsigned DCACHE_SET_ASSOC = 2
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  logic                        scrub_trigger_i, // Set to 1'b0 to disable
  output logic                        bit_corrected_o,
  output logic                        uncorrectable_o,

  // Input signals from others accessing memory bank
  input  logic   [DCACHE_SET_ASSOC-1:0] intc_req_i,
  input  logic                        intc_we_i,
  input  logic [AddrWidth-1:0] intc_add_i,
  input  std_cache_pkg::cl_be_SRAM_t  intc_be_i,
  input  std_cache_pkg::cache_line_SRAM_t intc_wdata_i,
  output std_cache_pkg::cache_line_SRAM_t [DCACHE_SET_ASSOC-1:0]intc_rdata_o,

  // Output directly to bank
  output logic [DCACHE_SET_ASSOC-1:0] bank_req_o,
  output logic                        bank_we_o,
  output logic [AddrWidth-1:0] bank_add_o,
  output std_cache_pkg::cache_line_SRAM_t bank_wdata_o,
  input  std_cache_pkg::cache_line_SRAM_t [DCACHE_SET_ASSOC-1:0] bank_rdata_i,
  output std_cache_pkg::cl_be_SRAM_t bank_be_o


);
// TODO vldrty add per cache
// Note TODO, currently is this module deactivted 


  logic [SECDEC_DIVISIONS_DATA-1:0][                 1:0] ecc_err_s;

  logic [                 1:0] ecc_err_t;
  logic [1:0] ecc_err;

  logic[DCACHE_SET_ASSOC-1:0] scrub_req, scrub_req_d, scrub_req_q;
  logic                        scrub_we;
  logic [AddrWidth-1:0] scrub_add;
  std_cache_pkg::cache_line_SRAM_t scrub_wdata;
  std_cache_pkg::cache_line_SRAM_t [DCACHE_SET_ASSOC-1:0] scrub_rdata;

  typedef enum logic [2:0] {Idle, Read, Write} scrub_state_e;

  scrub_state_e state_s_d, state_s_q;

  logic [AddrWidth-1:0] working_add_d, working_add_q;
  assign scrub_add = working_add_q;

  assign bank_req_o   = (scrub_trigger_i && (state_s_q == Read || state_s_q == Write) && (|intc_req_i) == 1'b0) ? 2**scrub_req : intc_req_i;
  assign intc_rdata_o = bank_rdata_i;
  assign scrub_rdata  = bank_rdata_i;

  always_comb begin : proc_bank_assign
    // By default, bank is connected to outside
    bank_we_o    = intc_we_i;
    bank_add_o   = intc_add_i;
    bank_wdata_o = intc_wdata_i;
    bank_be_o    = intc_be_i;

    // If scrubber active and outside is not, do scrub
    if (scrub_trigger_i && (state_s_q == Read || state_s_q == Write) && (|intc_req_i) == 1'b0) begin
     
      bank_we_o    = scrub_we;
      bank_add_o   = scrub_add;
      bank_wdata_o = scrub_wdata;
      bank_be_o    = '1;
    end
  end

  for (genvar j = 0; j<SECDEC_DIVISIONS_DATA;j++) begin
      hsiao_ecc_cor #(
      .DataWidth (SECDEC_BLOCK_SIZE)
      ) ecc_corrector (
      .in        ( scrub_rdata[scrub_req_q].data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] ),
      .out       ( scrub_wdata.data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] ),
      .syndrome_o(),
      .err_o     ( ecc_err_s[j]     )
      );
  end

  hsiao_ecc_cor #(
    .DataWidth (DCACHE_TAG_WIDTH)
  ) ecc_corrector (
  .in        ( scrub_rdata[scrub_req_q].tag),
  .out       ( scrub_wdata.tag),
  .syndrome_o(),
  .err_o     ( ecc_err_t     )
  );


  assign scrub_wdata.dirty =scrub_rdata[scrub_req_q].dirty;
  assign scrub_wdata.valid =scrub_rdata[scrub_req_q].valid;
  


  
  assign ecc_err = (|ecc_err_s) | ecc_err_t;

  always_comb begin : proc_FSM_logic
    state_s_d       = state_s_q;
    scrub_req     = scrub_req_q;
    scrub_we      = 1'b0;
    working_add_d = working_add_q;
    scrub_req_d = scrub_req_q;
    bit_corrected_o = 1'b0;
    uncorrectable_o = 1'b0;

    if (state_s_q == Idle) begin
      // Switch to read state if triggered to scrub
      if (scrub_trigger_i) begin // TODO maybe add time delay
        state_s_d = Read;
      end

    end else if (state_s_q == Read) begin
      // Request read to scrub
      scrub_req = scrub_req_q;
      // Request only active if outside is inactive
      if (intc_req_i == 1'b0) begin
        state_s_d = Write;
      end

    end else if (state_s_q == Write) begin
      if (ecc_err[0] == 1'b0) begin   // No correctable Error            TODO make a loop and not do |ecc_err
        // Return to idle state
        state_s_d       = Idle;
        scrub_req_d = (scrub_req_q ) % DCACHE_SET_ASSOC;
        if (scrub_req_q== DCACHE_SET_ASSOC-1) begin //count of the req and then afterwards count up the address
          working_add_d = (working_add_q + 1) % BankSize; // increment address
        end
        uncorrectable_o = ecc_err[1];

      end else begin                  // Correctable Error
        // Write corrected version
        scrub_req = scrub_req_q;
        scrub_we  = 1'b1;

        // INTC interference - retry read and write
        if (intc_req_i == 1'b1) begin
          state_s_d = Read;
        end else begin                // Error corrected
          state_s_d       = Idle;
          scrub_req_d = (scrub_req_q + 1) % DCACHE_SET_ASSOC;
          if (scrub_req_q== DCACHE_SET_ASSOC-1) begin //count of the req and then afterwards count up the address
            working_add_d = (working_add_q + 1) % BankSize; // increment address
          end
          bit_corrected_o = 1'b1;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bank_add
    if(!rst_ni) begin
      working_add_q <= '0;
      scrub_req_q <= '0;
    end else begin
      working_add_q <= working_add_d;
      scrub_req_q <= scrub_req_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_FSM
    if(!rst_ni) begin
      state_s_q <= Idle;
    end else begin
      state_s_q <= state_s_d;
    end
  end

endmodule
