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

module ecc_scrubber #(
  parameter int unsigned BankSize       = 256,
  parameter bit          UseExternalECC = 0,
  parameter int unsigned DataWidth      = 39,
  parameter int unsigned ProtWidth      = 7,
  parameter int unsigned Assoc          = 1,
  parameter type          line_t        = logic [DataWidth-1:0]
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  logic                        scrub_trigger_i, // Set to 1'b0 to disable
  output logic                        bit_corrected_o,
  output logic                        uncorrectable_o,

  // Input signals from others accessing memory bank
  input  logic [           Assoc-1:0] intc_req_i,
  input  logic                        intc_we_i,
  input  logic [$clog2(BankSize)-1:0] intc_add_i,
  input  line_t                       intc_wdata_i,
  output line_t [          Assoc-1:0] intc_rdata_o,

  // Output directly to bank
  output logic [           Assoc-1:0] bank_req_o,
  output logic                        bank_we_o,
  output logic [$clog2(BankSize)-1:0] bank_add_o,
  output line_t                       bank_wdata_o,
  input  line_t [          Assoc-1:0] bank_rdata_i,

  // If using external ECC
  output line_t [          Assoc-1:0] ecc_out_o,
  input  line_t [          Assoc-1:0] ecc_in_i,
  input  logic [      Assoc-1:0][1:0] ecc_err_i
);

  logic [      Assoc-1:0][1:0] ecc_err;
  int assoc_c = 0;
  logic [           Assoc-1:0] scrub_req;
  logic                        scrub_we;
  logic [$clog2(BankSize)-1:0] scrub_add;
  line_t                       scrub_wdata;
  line_t [          Assoc-1:0] temp_scrub_wdata;
  line_t [          Assoc-1:0] scrub_rdata;

  typedef enum logic [2:0] {Idle, Read, Write} scrub_state_e;

  scrub_state_e state_d, state_q;

  logic [$clog2(BankSize)-1:0] working_add_d, working_add_q;
  assign scrub_add = working_add_q;

  assign intc_rdata_o = bank_rdata_i;
  assign scrub_rdata  = bank_rdata_i;

  always_comb begin : proc_bank_assign
    // By default, bank is connected to outside
    bank_we_o    = intc_we_i;
    bank_add_o   = intc_add_i;
    bank_wdata_o = intc_wdata_i;
    bank_req_o   = intc_req_i;

    // If scrubber active and outside is not, do scrub
    if ( (state_q == Read || state_q == Write) && |intc_req_i === 1'b0) begin
      bank_we_o    = scrub_we;
      bank_add_o   = scrub_add;
      bank_wdata_o = scrub_wdata;
      bank_req_o   = scrub_req;
    end
  end

  if (UseExternalECC) begin : gen_external_ecc
    assign ecc_err = ecc_err_i;
    assign ecc_out_o = scrub_rdata;
    assign temp_scrub_wdata = ecc_in_i;
  end else begin : gen_internal_ecc
    assign ecc_out_o = '0;

    for (genvar assoc = 0; assoc<Assoc; ++assoc)begin : gen_error_correct_assoc
      hsiao_ecc_cor #(
        .DataWidth (DataWidth-ProtWidth),
        .ProtWidth (ProtWidth)
      ) ecc_corrector (
        .in        ( scrub_rdata[assoc] ),
        .out       ( temp_scrub_wdata[assoc] ),
        .syndrome_o(),
        .err_o     ( ecc_err[assoc]     )
      );
    end
  end

  always_comb begin
    for (int assoc=0; assoc<Assoc; ++assoc)begin
      if ((|ecc_err[assoc])===1'b1 )begin
        scrub_wdata = temp_scrub_wdata[assoc];
        assoc_c = assoc;
        break;
      end
    end
  end

  always_comb begin : proc_FSM_logic
    state_d       = state_q;
    scrub_req     = 1'b0;
    scrub_we      = 1'b0;
    working_add_d = working_add_q;
    bit_corrected_o = 1'b0;
    uncorrectable_o = 1'b0;

    if (state_q == Idle) begin
      // Switch to read state if triggered to scrub
      if (scrub_trigger_i) begin
        state_d = Read;
      end

    end else if (state_q == Read) begin
      // Request read to scrub
      scrub_req = '1;
      // Request only active if outside is inactive
      if (intc_req_i == 1'b0) begin
        state_d = Write;
      end

    end else if (state_q == Write) begin
      if (ecc_err[assoc_c][0] !== 1'b1) begin   // No correctable Error
        // Return to idle state
        state_d       = Idle;
        working_add_d = (working_add_q + 1) % BankSize; // increment address
        uncorrectable_o = ecc_err[assoc_c][1];

      end else begin                  // Correctable Error
        // Write corrected version
        scrub_req = 1<<assoc_c;
        scrub_we  = 1'b1;

        // INTC interference - retry read and write
        if (|intc_req_i === 1'b1) begin
          state_d = Read;
        end else begin                // Error corrected
          state_d       = Idle;
          working_add_d = (working_add_q + 1) % BankSize; // increment address
          bit_corrected_o = 1'b1;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bank_add
    if(!rst_ni) begin
      working_add_q <= '0;
    end else begin
      working_add_q <= working_add_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_FSM
    if(!rst_ni) begin
      state_q <= Idle;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
