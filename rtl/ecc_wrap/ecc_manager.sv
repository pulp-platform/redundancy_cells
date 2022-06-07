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
// ECC sram manager (loggs faults, triggers scrubber)

module ecc_manager #(
  parameter int unsigned NumBanks      = 6,
  parameter type         ecc_mgr_req_t = logic,
  parameter type         ecc_mgr_rsp_t = logic
) (
  input  logic                clk_i,
  input  logic                rst_ni,

  input  ecc_mgr_req_t        ecc_mgr_req,
  output ecc_mgr_rsp_t        ecc_mgr_rsp,

  input  logic [NumBanks-1:0] bank_faults_i,
  input  logic [NumBanks-1:0] scrub_fix_i,
  output logic [NumBanks-1:0] scrub_trigger_o,
  output logic [NumBanks-1:0][38:0] test_write_mask_no
);
  import ecc_manager_reg_pkg::*;

  logic [NumBanks-1:0][31:0] counter_value;

  ecc_manager_reg2hw_t reg2hw;
  ecc_manager_hw2reg_t hw2reg;

  ecc_manager_reg_top #(
    .reg_req_t ( ecc_mgr_req_t ),
    .reg_rsp_t ( ecc_mgr_rsp_t )
  ) i_registers (
    .clk_i     ( clk_i       ),
    .rst_ni    ( rst_ni      ),
    .reg_req_i ( ecc_mgr_req ),
    .reg_rsp_o ( ecc_mgr_rsp ),
    .reg2hw    ( reg2hw      ),
    .hw2reg    ( hw2reg      ),
    .devmode_i ( '0          )
  );

  for (genvar i = 0; i < NumBanks; i++) begin : gen_fault_increment
    // Count ECC fixes on access
    assign hw2reg.mismatch_count[i].d = reg2hw.mismatch_count[i].q + 1;
    assign hw2reg.mismatch_count[i].de = bank_faults_i[i];

    // Count ECC fixes on scrub
    assign hw2reg.scrub_fix_count[i].d = reg2hw.scrub_fix_count[i].q + 1;
    assign hw2reg.scrub_fix_count[i].de = scrub_fix_i[i];

    // Assign testing mask
    assign test_write_mask_no[i][31:0] = reg2hw.write_mask_data_n[i];
    assign test_write_mask_no[i][38:32] = reg2hw.write_mask_ecc_n[i];

    // Instantiate scrub trigger counter
    assign scrub_trigger_o[i] = counter_value[i] == reg2hw.scrub_interval.q;
    counter #(
      .WIDTH           ( 32   ),
      .STICKY_OVERFLOW ( 1'b0 )
    ) i_scrub_counter (
      .clk_i,
      .rst_ni,
      .clear_i   ( reg2hw.scrub_interval.q == '0 ),
      .en_i      ( reg2hw.scrub_interval.q != '0 ),
      .load_i    ( counter_value[i] == reg2hw.scrub_interval.q ),
      .down_i    ( 1'b0 ),
      .d_i       ( '0 ),
      .q_o       ( counter_value[i] ),
      .overflow_o()
    );
  end

endmodule
