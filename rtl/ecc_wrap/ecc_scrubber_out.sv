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
//   - the out scrubber itself does't correct data, the ecc_sram_wrap itself will write the corrected read data back to sram

module ecc_scrubber_out #(
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  parameter int unsigned TagWidth       = 32,
  parameter int unsigned DataWidth      = 128,
  parameter int unsigned TagDepth       = 256,
  parameter int unsigned DataDepth      = 2048,
  parameter type         error_info_per_way_t = logic,
  // Dependency parameters:
  parameter int unsigned DataTagDepthFactor  = DataDepth/TagDepth // should equal to the block number for each index

  
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  logic                        scrub_trigger_i, // Set to 1'b0 to disable
  output logic                        bit_corrected_o,
  output logic                        uncorrectable_o,

  // Input signals from others accessing tag memory bank
  input  logic                        tag_intc_req_i,
  output logic                        tag_intc_gnt_o,
  input  logic                        tag_intc_we_i,
  input  logic                        tag_intc_be_i,
  input  logic [$clog2(TagDepth)-1:0] tag_intc_add_i,
  input  logic [       TagWidth-1:0]  tag_intc_wdata_i,
  output logic [       TagWidth-1:0]  tag_intc_rdata_o,
  output logic                        tag_intc_multi_err_o,

  // Input signals from others accessing data memory bank
  input  logic                        data_intc_req_i,
  output logic                        data_intc_gnt_o,
  input  logic                        data_intc_we_i,
  input  logic [(Cfg.BlockSize + 8 - 32'd1) / 8-1:0] data_intc_be_i,
  input  logic [$clog2(DataDepth)-1:0] data_intc_add_i,
  input  logic [       DataWidth-1:0] data_intc_wdata_i,
  output logic [       DataWidth-1:0] data_intc_rdata_o,
  output logic                        data_intc_multi_err_o,

  // Output directly to tag bank
  output logic                        tag_bank_req_o,
  input  logic                        tag_bank_gnt_i,
  output logic                        tag_bank_we_o,
  output logic                        tag_bank_be_o,
  output logic [$clog2(TagDepth)-1:0] tag_bank_add_o,
  output logic [       TagWidth-1:0]  tag_bank_wdata_o,
  input  logic [       TagWidth-1:0]  tag_bank_rdata_i,

  // Output directly to data bank
  output logic                        data_bank_req_o,
  input  logic                        data_bank_gnt_i,
  output logic                        data_bank_we_o,
  output logic [(Cfg.BlockSize + 8 - 32'd1) / 8-1:0] data_bank_be_o,
  output logic [$clog2(DataDepth)-1:0] data_bank_add_o,
  output logic [       DataWidth-1:0] data_bank_wdata_o,
  input  logic [       DataWidth-1:0] data_bank_rdata_i,

  // Input external ECC result
  input  error_info_per_way_t  ecc_err_i
);

  logic single_error;
  logic multi_error;


  logic                        scrub_req;
  logic                        scrub_we;
  logic [$clog2(DataDepth)-1:0] scrub_add;
  // logic [       DataWidth-1:0] scrub_wdata;
  logic [       TagWidth-1:0]  scrub_tag_rdata;
  logic [       DataWidth-1:0] scrub_data_rdata;

  typedef enum logic [2:0] {Idle, Read, Check} scrub_state_e;

  scrub_state_e state_d, state_q;

  logic [$clog2(DataDepth)-1:0] working_add_d, working_add_q; // use data addr as it should be >= tag addr size, because the block number per index
  
  logic tag_rdata_en, tag_rdata_en_q;
  logic data_rdata_en, data_rdata_en_q;
  logic data_wdata_en, data_wdata_en_q;
  logic data_en_q;
  logic [TagWidth-1:0]  tag_rdata_q;
  logic [DataWidth-1:0] data_rdata_q;
  logic                 tag_intc_multi_err_q;
  logic                 data_intc_multi_err_q;

  assign tag_rdata_en   = tag_intc_req_i  & tag_bank_gnt_i  & ~tag_intc_we_i;
  assign data_rdata_en  = data_intc_req_i & data_bank_gnt_i & ~data_intc_we_i;
  assign data_wdata_en  = data_intc_req_i & data_bank_gnt_i &  data_intc_we_i;
  assign data_en_q      = data_rdata_en_q | data_wdata_en_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      tag_rdata_q <= '0;
      tag_intc_multi_err_q <= '0;
    end else if (tag_rdata_en_q) begin
      tag_rdata_q <= tag_bank_rdata_i;
      tag_intc_multi_err_q <= ecc_err_i.tag_sram_multi_error;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      data_rdata_q <= '0;
    end else if (data_rdata_en_q) begin
      data_rdata_q <= data_bank_rdata_i;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      data_intc_multi_err_q <= '0;
    end else if (data_en_q) begin
      data_intc_multi_err_q <= ecc_err_i.data_sram_multi_error;
    end
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      tag_rdata_en_q  <= 1'b0;
      data_rdata_en_q <= 1'b0;
      data_wdata_en_q <= 1'b0;
    end else begin
      tag_rdata_en_q  <= tag_rdata_en;
      data_rdata_en_q <= data_rdata_en;
      data_wdata_en_q <= data_wdata_en;
    end
  end


  assign scrub_add = working_add_q;

  assign tag_bank_req_o     = tag_intc_req_i  || scrub_req;
  assign tag_intc_gnt_o     = tag_bank_gnt_i;
  assign tag_intc_rdata_o      = tag_rdata_en_q  ? tag_bank_rdata_i : tag_rdata_q;
  assign tag_intc_multi_err_o  = tag_rdata_en_q  ? ecc_err_i.tag_sram_multi_error : tag_intc_multi_err_q;

  assign data_bank_req_o    = data_intc_req_i || scrub_req;
  assign data_intc_gnt_o    = data_bank_gnt_i;
  assign data_intc_rdata_o     = data_rdata_en_q ? data_bank_rdata_i : data_rdata_q;
  // for data sram write, because the read modify wrtie for partial block write exist, may have error respones the next cycle of the write gnt
  assign data_intc_multi_err_o = data_en_q ? ecc_err_i.data_sram_multi_error : data_intc_multi_err_q;

  assign scrub_tag_rdata  = tag_bank_rdata_i;
  assign scrub_data_rdata = data_bank_rdata_i;

  always_comb begin : proc_tag_bank_assign
    // By default, bank is connected to outside
    tag_bank_we_o    = tag_intc_we_i;
    tag_bank_be_o    = tag_intc_be_i;
    tag_bank_add_o   = tag_intc_add_i;
    tag_bank_wdata_o = tag_intc_wdata_i;

    // If scrubber active and outside is not, do scrub
    if ( (state_q == Read || state_q == Check) && (tag_intc_req_i == 1'b0) && (data_intc_req_i == 1'b0)) begin
      tag_bank_we_o    = 1'b0;
      tag_bank_be_o    = '0;
      tag_bank_add_o   = scrub_add[$clog2(DataDepth)-1:$clog2(DataTagDepthFactor)];
    end
  end

  always_comb begin : proc_data_bank_assign
    // By default, bank is connected to outside
    data_bank_we_o    = data_intc_we_i;
    data_bank_be_o    = data_intc_be_i;
    data_bank_add_o   = data_intc_add_i;
    data_bank_wdata_o = data_intc_wdata_i;

    // If scrubber active and outside is not, do scrub
    if ( (state_q == Read || state_q == Check) && (tag_intc_req_i == 1'b0) && data_intc_req_i == 1'b0) begin
      data_bank_we_o    = 1'b0;
      data_bank_be_o    = '0;
      data_bank_add_o   = scrub_add;
    end
  end

  always_comb begin : proc_FSM_logic
    state_d       = state_q;
    scrub_req     = 1'b0;
    working_add_d = working_add_q;
    bit_corrected_o = 1'b0;
    uncorrectable_o = 1'b0;

    if (state_q == Idle) begin
      // Switch to read state if triggered to scrub
      if (scrub_trigger_i) begin
        state_d = Read;
      end

    end else if (state_q == Read) begin
      // Request only active if outside is inactive, and the ecc_sram is ready
      if ((tag_intc_req_i == 1'b0) && 
          (tag_bank_gnt_i == 1'b1) &&
          (data_intc_req_i == 1'b0) && 
          (data_bank_gnt_i == 1'b1)
          ) begin
        // Request read to scrub
        scrub_req = 1'b1;
        state_d = Check;
      end

    end else if (state_q == Check) begin
      // Return to idle state
      state_d         = Idle;
      working_add_d   = (working_add_q + 1) % DataDepth; // increment address
      bit_corrected_o = single_error;
      uncorrectable_o = multi_error;
    end
  end
  
  // TODO: tag sram has uncorrectable error, interrupt
  // TODO: data sram has uncorrectable error, interrupt, has addr info


  assign single_error = ecc_err_i.tag_sram_single_error | ecc_err_i.data_sram_single_error;
  assign multi_error  = ecc_err_i.tag_sram_multi_error  | ecc_err_i.data_sram_multi_error;


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
