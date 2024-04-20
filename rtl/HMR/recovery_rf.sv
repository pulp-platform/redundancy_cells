// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Francesco Conti - f.conti@unibo.it                         //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31x 32 bit wide registers. Register 0   //
//                 is fixed to 0. This register file is based on flip-flops.  //
//                 Also supports the fp-register file now if FPU=1            //
//                 If PULP_ZFINX is 1, floating point operations take values  //
//                 from the X register file                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module recovery_rf #(
  parameter  int unsigned ECCEnabled        = 0,
  parameter  int unsigned NumRdPorts        = 3,
  parameter  int unsigned NumWrPorts        = 2,
  parameter  int unsigned AddrWidth         = 5,
  parameter  int unsigned NonProtectedWidth = 32,
  parameter  int unsigned ParityWidth       = $clog2(NonProtectedWidth)+2,
  parameter  int unsigned ProtectedWidth    = NonProtectedWidth + ParityWidth,
  parameter  int unsigned FPU               = 0,
  parameter  bit          SingleCycleRecovery = 1'b0,
  parameter  type         regfile_write_t   = logic,
  parameter  type         regfile_raddr_t   = logic,
  parameter  type         regfile_rdata_t   = logic,
  localparam int unsigned NumWords = 2 ** AddrWidth,
  localparam int unsigned DataWidth         = ( ECCEnabled ) ? ProtectedWidth
                                                             : NonProtectedWidth
)(
  // Clock and Reset
  input logic clk_i,
  input logic rst_ni,
  output logic [NumWords-1:0][NonProtectedWidth-1:0] rf_mem_o,
  //Read port
  input  logic [NumRdPorts-1:0][AddrWidth-1:0]         raddr_i,
  output logic [NumRdPorts-1:0][NonProtectedWidth-1:0] rdata_o,
  // Write port
  input logic [NumWrPorts-1:0][AddrWidth-1:0]         waddr_i,
  input logic [NumWrPorts-1:0][NonProtectedWidth-1:0] wdata_i,
  input logic [NumWrPorts-1:0]                        we_i
);

  logic [NumWrPorts-1:0][NonProtectedWidth-1:0] mem;
  logic [NumWrPorts-1:0][DataWidth-1:0] ecc_mem, wdata;
  logic [NumRdPorts-1:0][DataWidth-1:0] rdata;
  logic [NumWrPorts-1:0][NumWords-1:0] we_dec;

  if (ECCEnabled) begin : gen_ecc
    for (genvar i = 0; i < NumWrPorts;  i++) begin
      hsiao_ecc_enc #(
        .DataWidth ( NonProtectedWidth ),
        .ProtWidth ( ParityWidth )
      ) i_ecc_encoder (
        .in  ( wdata_i[i] ),
        .out ( wdata[i] )
      );
    end

    for (genvar i = 0; i < NumRdPorts; i++) begin
      hsiao_ecc_dec #(
        .DataWidth ( NonProtectedWidth ),
        .ProtWidth ( ParityWidth )
      ) i_ecc_decoder (
        .in         ( rdata[i]   ),
        .out        ( rdata_o[i] ),
        .syndrome_o ( ),
        .err_o      ( )
      );
    end

    if (SingleCycleRecovery) begin: gen_full_rf_access
      for (genvar i = 0; i < NumWords; i++) begin
        hsiao_ecc_dec #(
        .DataWidth ( NonProtectedWidth ),
        .ProtWidth ( ParityWidth )
      ) i_ecc_full_decoder (
        .in         ( ecc_mem[i]  ),
        .out        ( rf_mem_o[i] ),
        .syndrome_o ( ),
        .err_o      ( )
      );
      end
    end else begin: gen_no_full_rf_access
      assign rf_mem_o = '0;
    end
  end else begin : no_ecc_region
    for (genvar i = 0; i < NumWrPorts; i++)
      assign wdata[i] = wdata_i[i];

    for (genvar i = 0; i < NumWords; i++)
      assign mem[i] = ecc_mem[i];

    for (genvar i = 0; i < NumRdPorts; i++)
      assign rdata_o[i] = rdata[i];
  end

  for (genvar j = 0; j < NumWrPorts; j++) begin
    for (genvar i = 0; i < NumWords; i++) begin
      assign we_dec[j][i] = (waddr_i[j] == i) ? we_i[j] : 1'b0;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin : register_write_behavioral
    if (~rst_ni) begin
      ecc_mem <= '{default: '0};
    end else begin
      for (int unsigned j = 0; j < NumWrPorts; j++) begin
        for (int unsigned i = 1; i < NumWords; i++) begin
          if (we_dec[j][i]) begin
            ecc_mem[i] <= wdata[j];
          end
        end
      end
    end
  end

  for (genvar i = 0; i < NumRdPorts; i++) begin
    assign rdata[i] = ecc_mem[raddr_i[i]];
  end

endmodule
