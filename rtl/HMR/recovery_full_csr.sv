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
 * Recovery Control Status Registers
 * ECC-protected register that stores the CSRs values from the cores
 *
 */

module recovery_full_csr
  import rapid_recovery_pkg::*;
#(
  parameter  int unsigned ECCEnabled        = 0,
  parameter  int unsigned NonProtectedWidth = 32,
  parameter  int unsigned ParityWidth       = $clog2(NonProtectedWidth)+2,
  parameter  int unsigned ProtectedWidth    = NonProtectedWidth + ParityWidth,
  parameter  int unsigned AddrWidth         = 12,
  parameter  int unsigned NumCsr            = 1,
  parameter  int unsigned NumWrPorts        = 1,
  parameter  int unsigned NumRdPorts        = 1,
  parameter  bit [NumCsr][AddrWidth-1:0] CsrList = '{'h000},
  parameter      type     csr_intf_t        = logic,
  parameter      type     exception_t       = logic,
  parameter      type     scoreboard_entry_t = logic,
  localparam int unsigned ExceptionWidth = $bits(exception_t),
  localparam int unsigned ExceptionParityWidth = ( ECCEnabled ) ?
                                                 $clog2(ExceptionWidth) + 2 : '0,
  localparam int unsigned TotExceptionWidth = ExceptionWidth + ExceptionParityWidth,
  localparam int unsigned ScoreBoardWidth = $bits(scoreboard_entry_t),
  localparam int unsigned ScoreBoardParityWidth = ( ECCEnabled ) ?
                                                 $clog2(ScoreBoardWidth) + 2 : '0,
  localparam int unsigned TotScoreBoardWidth = ScoreBoardWidth + ScoreBoardParityWidth,
  localparam int unsigned CsrIdWidth = $clog2(NumCsr),
  localparam int unsigned DataWidth  = ( ECCEnabled ) ? ProtectedWidth
                                                      : NonProtectedWidth
) (
  input  logic clk_i ,
  input  logic rst_ni,
  input  logic read_enable_i,
  input  logic write_enable_i,
  input  logic [CsrIdWidth-1:0] csr_id_i,
  input  csr_intf_t [NumWrPorts-1:0] backup_csr_i,
  output csr_intf_t [NumRdPorts-1:0] recovery_csr_o
);

// We store the addresses of the available CSRs in
// a Look-Up Table that we can use for the rapid recovery
logic [NumCsr-1:0][AddrWidth-1:0] csr_lut;
always_ff @(posedge clk_i, negedge rst_ni) begin
  if (~rst_ni) begin
    csr_lut <= '0;
  end else begin
    for (int i = 0; i < NumCsr; i++)
      csr_lut[i] <= CsrList[i];
  end
end

logic [NumCsr-1:0][DataWidth-1:0] csr_mem;
logic [NumRdPorts-1:0][DataWidth-1:0] rdata;
logic [NumWrPorts-1:0][DataWidth-1:0] wdata;
logic [DataWidth-1:0] program_counter_d, program_counter_q;
logic [TotExceptionWidth-1:0] exception_d, exception_q;
logic [TotScoreBoardWidth-1:0] scoreboard_entry_d, scoreboard_entry_q;

if (ECCEnabled) begin: gen_ecc_csr
  for (genvar i = 0; i < NumWrPorts; i++) begin
    hsiao_ecc_enc #(
      .DataWidth ( NonProtectedWidth ),
      .ProtWidth ( ParityWidth )
    ) i_csr_ecc_encoder (
      .in  ( backup_csr_i[i].data ),
      .out ( wdata[i]   )
    );

    if (i == 0) begin
      hsiao_ecc_enc #(
        .DataWidth ( NonProtectedWidth ),
        .ProtWidth ( ParityWidth )
      ) i_pc_ecc_encoder (
        .in  ( backup_csr_i[i].program_counter ),
        .out ( program_counter_d )
      );

      hsiao_ecc_enc #(
        .DataWidth ( ExceptionWidth ),
        .ProtWidth ( ExceptionParityWidth )
      ) i_exception_ecc_encoder (
        .in  ( backup_csr_i[0].exception ),
        .out ( exception_d )
      );

      hsiao_ecc_enc #(
        .DataWidth ( ScoreBoardWidth ),
        .ProtWidth ( ScoreBoardParityWidth )
      ) i_scoreboard_entry_ecc_encoder (
        .in  ( backup_csr_i[0].scoreboard_entry ),
        .out ( scoreboard_entry_d )
      );
    end
  end

  for (genvar i = 0; i < NumRdPorts; i++) begin
    hsiao_ecc_dec #(
      .DataWidth ( NonProtectedWidth ),
      .ProtWidth ( ParityWidth )
    ) i_csr_ecc_decoder (
      .in         ( rdata[i] ),
      .out        ( recovery_csr_o[i].data ),
      .syndrome_o ( ),
      .err_o      ( )
    );

    if (i == 0) begin
      hsiao_ecc_dec #(
        .DataWidth ( NonProtectedWidth ),
        .ProtWidth ( ParityWidth )
      ) i_pc_ecc_decoder (
        .in         ( program_counter_q ),
        .out        ( recovery_csr_o[i].program_counter ),
        .syndrome_o ( ),
        .err_o      ( )
      );

      hsiao_ecc_dec #(
        .DataWidth ( ExceptionWidth ),
        .ProtWidth ( ExceptionParityWidth )
      ) i_exception_ecc_decoder (
        .in         ( exception_q ),
        .out        ( recovery_csr_o[i].exception ),
        .syndrome_o ( ),
        .err_o      ( )
      );

      hsiao_ecc_dec #(
        .DataWidth ( ScoreBoardWidth ),
        .ProtWidth ( ScoreBoardParityWidth )
      ) i_scoreboard_entry_ecc_decoder (
        .in         ( scoreboard_entry_q ),
        .out        ( recovery_csr_o[0].scoreboard_entry ),
        .syndrome_o ( ),
        .err_o      ( )
      );
    end else begin
      assign recovery_csr_o[i].program_counter = '0;
      assign recovery_csr_o[i].exception = '0;
    end
  end

end else begin: gen_no_ecc_csr
  assign program_counter_d = backup_csr_i[0].program_counter;
  assign exception_d = backup_csr_i[0].exception;
  assign scoreboard_entry_d = backup_csr_i[0].scoreboard_entry;

  for (genvar i = 0; i < NumWrPorts; i++)
    assign wdata[i] = backup_csr_i[i].data;

  for (genvar i = 0; i < NumRdPorts; i++) begin
    assign recovery_csr_o[i].data = rdata[i];
    if (i == 0) begin
      assign recovery_csr_o[i].program_counter = program_counter_q;
      assign recovery_csr_o[i].exception = exception_q;
      assign recovery_csr_o[i].scoreboard_entry = scoreboard_entry_q;
    end else begin
      assign recovery_csr_o[i].program_counter = '0;
      assign recovery_csr_o[i].exception = '0;
      assign recovery_csr_o[i].scoreboard_entry = '0;
    end
  end
end

logic [NumWrPorts-1:0][NumCsr-1:0] write_enable;
for (genvar j = 0; j < NumWrPorts; j++) begin
  for (genvar i = 0; i < NumCsr; i++) begin
    assign write_enable[j][i] = (backup_csr_i[j].addr == csr_lut[i]) ?
                                (write_enable_i & backup_csr_i[j].write) : 1'b0;
  end
end

// CSR regfile
always_ff @(posedge clk_i, negedge rst_ni) begin : register_write_behavioral
  if (~rst_ni) begin
    csr_mem <= '{default: '0};
  end else begin
    for (int unsigned j = 0; j < NumWrPorts; j++) begin
      for (int unsigned i = 0; i < NumCsr; i++) begin
        if (write_enable[j][i]) begin
          csr_mem[i] <= wdata[j];
        end
      end
    end
  end
end

// Program counter, last scoreboard entry, and
// commit exception are stored separately
always_ff @(posedge clk_i, negedge rst_ni) begin
  if (~rst_ni) begin
    program_counter_q <= '0;
    exception_q <= '0;
    scoreboard_entry_q <= '0;
  end else begin
    if (write_enable_i) begin
      program_counter_q <= program_counter_d;
      exception_q <= exception_d;
      scoreboard_entry_q <= scoreboard_entry_d;
    end
  end
end

for (genvar i = 0; i < NumRdPorts; i++) begin
  assign recovery_csr_o[i].addr = csr_lut[csr_id_i + i];
  assign recovery_csr_o[i].write = ~read_enable_i;
  assign rdata[i] = csr_mem[recovery_csr_o[i].addr];
end

endmodule : recovery_full_csr
