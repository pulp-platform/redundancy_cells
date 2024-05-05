/* Copyright 2020 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 * 
 * Dual Modular Address Generator
 * Generates addresses for RF refill 
 * 
 */

module DMR_address_generator
  import rapid_recovery_pkg::*;
#(
  parameter rapid_recovery_cfg_t RrCfg = rapid_recovery_pkg::RrDefaultCfg,
  parameter int unsigned AddrWidth = 5,
  parameter int unsigned NumIntRfRdPorts = 2,
  parameter int unsigned NumFpRfRdPorts = 2,
  parameter int unsigned NumCsr = 4,
  parameter int unsigned NumCsrRdPorts = 1,
  localparam int unsigned NumAddr = 2 ** (AddrWidth - 1),
  localparam int unsigned CsrIdWidth = $clog2(NumCsr)
)(
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clear_i,
  input  logic enable_i,
  output logic done_o,
  output logic fatal_o,
  output logic [AddrWidth-1:0] int_rf_address_o,
  output logic [AddrWidth-1:0] fp_rf_address_o,
  output logic [CsrIdWidth-1:0] csr_id_o
);

localparam int unsigned NumVotingSignals = 3;
localparam int unsigned NumTMRResults = 1;
localparam int unsigned ArrayWidth = NumVotingSignals + NumTMRResults;

logic int_regfile_done, fp_regfile_done, csr_done;
logic int_rf_addr_count_err, fp_rf_addr_count_err, csr_id_err;
logic [NumVotingSignals-1:0] int_rf_addr_count_rst, fp_rf_addr_count_rst, csr_id_rst;
logic [ArrayWidth-1:0][AddrWidth-1:0] int_rf_addr_count, fp_rf_addr_count;
logic [ArrayWidth-1:0][CsrIdWidth-1:0] csr_id;

for (genvar i = 0; i < NumVotingSignals; i++) begin: gen_addr_generators
  if (RrCfg.IntRegFileBackupEnable) begin: gen_int_regfile_addr_gen
    always_ff @(posedge clk_i, negedge  rst_ni) begin
      if (~rst_ni) begin
        int_rf_addr_count [i] <= '0;
      end else begin
        if (clear_i || int_rf_addr_count_rst [i])
          int_rf_addr_count [i] <= '0;
        else if (enable_i)
          int_rf_addr_count [i] <= int_rf_addr_count [i] + 1;
        else
          int_rf_addr_count [i] <= int_rf_addr_count [i];
      end
    end
    assign int_rf_addr_count_rst [i] = ( int_rf_addr_count [i] == NumAddr/NumIntRfRdPorts - 1) ? 1'b1 : 1'b0;
  end else begin: gen_no_int_regfile_addr_gen
    assign int_rf_addr_count[i] = '0;
    assign int_rf_addr_count_rst[i] = '1;
  end

  if (RrCfg.FpRegFileBackupEnable) begin: gen_fp_regfile_addr_gen
    always_ff @(posedge clk_i, negedge  rst_ni) begin
      if (~rst_ni) begin
        fp_rf_addr_count [i] <= '0;
      end else begin
        if (clear_i || fp_rf_addr_count_rst [i])
          fp_rf_addr_count [i] <= '0;
        else if (enable_i)
          fp_rf_addr_count [i] <= fp_rf_addr_count [i] + 1;
        else
          fp_rf_addr_count [i] <= fp_rf_addr_count [i];
      end
    end
    assign fp_rf_addr_count_rst [i] = ( fp_rf_addr_count [i] == NumAddr/NumFpRfRdPorts - 1) ? 1'b1 : 1'b0;
  end else begin: gen_no_fp_rf_addr_generator
    assign fp_rf_addr_count[i] = '0;
    assign fp_rf_addr_count_rst[i] = '1;
  end

  if (RrCfg.FullCsrsBackupEnable) begin: gen_csr_regfile_addr_gen
    always_ff @(posedge clk_i, negedge  rst_ni) begin
      if (~rst_ni) begin
        csr_id [i] <= '0;
      end else begin
        if (clear_i || csr_id_rst [i])
          csr_id [i] <= '0;
        else if (enable_i)
          csr_id [i] <= csr_id [i] + 1;
        else
          csr_id [i] <= csr_id [i];
      end
    end
    assign csr_id_rst [i] = ( csr_id [i] == NumCsr/NumCsrRdPorts - 1) ? 1'b1 : 1'b0;
  end else begin: gen_no_csr_regfile_addr_gen
    assign csr_id[i] = '0;
    assign csr_id_rst[i] = '1;
  end
end

bitwise_TMR_voter #(
  .DataWidth ( AddrWidth ),
  .VoterType ( 0         )
) i_int_rf_address_voter (
  .a_i         ( int_rf_addr_count [0] ),
  .b_i         ( int_rf_addr_count [1] ),
  .c_i         ( int_rf_addr_count [2] ),
  .majority_o  ( int_rf_addr_count [3] ),
  .error_o     ( int_rf_addr_count_err ),
  .error_cba_o ( /* ... */      )
);

bitwise_TMR_voter #(
  .DataWidth ( AddrWidth ),
  .VoterType ( 0         )
) i_fp_rf_address_voter (
  .a_i         ( fp_rf_addr_count [0] ),
  .b_i         ( fp_rf_addr_count [1] ),
  .c_i         ( fp_rf_addr_count [2] ),
  .majority_o  ( fp_rf_addr_count [3] ),
  .error_o     ( fp_rf_addr_count_err ),
  .error_cba_o ( /* ... */      )
);

bitwise_TMR_voter #(
  .DataWidth ( CsrIdWidth ),
  .VoterType ( 0         )
) i_csr_id_counter_voter (
  .a_i         ( csr_id[0] ),
  .b_i         ( csr_id[1] ),
  .c_i         ( csr_id[2] ),
  .majority_o  ( csr_id[3] ),
  .error_o     ( csr_id_err),
  .error_cba_o ( /* ... */ )
);

always_ff @(posedge clk_i, negedge rst_ni) begin
  if (~rst_ni) begin
    int_regfile_done <= 1'b0;
    fp_regfile_done <= 1'b0;
    csr_done <= 1'b0;
  end else begin
    if (clear_i) begin
      int_regfile_done <= 1'b0;
      fp_regfile_done <= 1'b0;
      csr_done <= 1'b0;
    end else begin
      if (|csr_id_rst           ) csr_done <= 1'b1;
      if (|int_rf_addr_count_rst) int_regfile_done <= 1'b1;
      if (|fp_rf_addr_count_rst ) fp_regfile_done <= 1'b1;
    end
  end
end

assign int_rf_address_o = int_rf_addr_count [3]; // Result of TMR address voter
assign fp_rf_address_o = fp_rf_addr_count [3]; // Result of TMR address voter
assign csr_id_o = csr_id [3];
assign fatal_o = int_rf_addr_count_err | fp_rf_addr_count_err | csr_id_err; // Error from one of the two TMR voters
assign done_o = int_regfile_done & fp_regfile_done & csr_done;

endmodule : DMR_address_generator
