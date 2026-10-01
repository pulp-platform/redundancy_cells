// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "common_cells/assertions.svh"

module rel_stream_join #(
  parameter int unsigned N_INP        = 0,     // Number of input streams
  parameter bit          TmrHandshake = 1'b1,  // Use TMR for handshake signals
  parameter int unsigned VoterType    = 1,     // 0=Classical_MV, 1=KP_MV
  parameter int unsigned HsWidth      = TmrHandshake ? 3 : 1 // width of the handshake signals
) (
  /// Input streams valid handshakes
  input  logic [N_INP-1:0][HsWidth-1:0] inp_valid_i,
  /// Input streams ready handshakes
  output logic [N_INP-1:0][HsWidth-1:0] inp_ready_o,
  /// Output stream valid handshake
  output logic            [HsWidth-1:0] oup_valid_o,
  /// Output stream ready handshake
  input  logic            [HsWidth-1:0] oup_ready_i,
  /// Fault detection flag 
  output logic                          err_o
);

    logic [2:0][N_INP-1:0] inp_valid;
    logic [2:0][N_INP-1:0] inp_ready;
    logic [2:0]            oup_valid;
    logic [2:0]            oup_ready;
    logic [1:0]            faults   ;

    if(TmrHandshake) begin
        assign faults = '0;
        for(genvar i=0; i<3; i++) begin: gen_tmr
            for(genvar j=0; j<N_INP; j++) begin: gen_inp
                assign inp_valid  [i][j] = inp_valid_i[j][i];
                assign inp_ready_o[j][i] = inp_ready  [i][j];
            end
        end
        assign oup_ready   = oup_ready_i;
        assign oup_valid_o = oup_valid  ;
    end else begin
        TMR_voter_fail #(
            .VoterType(VoterType)
        ) i_oup_valid_voter (
            .a_i              (oup_valid[0]),
            .b_i              (oup_valid[1]),
            .c_i              (oup_valid[2]),
            .majority_o       (oup_valid_o ),
            .fault_detected_o (faults   [0])
        );
        bitwise_TMR_voter_fail #(
            .DataWidth(N_INP),
            .VoterType(VoterType)
        ) i_oup_ready_voter (
            .a_i              (inp_ready[0]),
            .b_i              (inp_ready[1]),
            .c_i              (inp_ready[2]),
            .majority_o       (inp_ready_o ),
            .fault_detected_o (faults   [1])
        );
        for(genvar i=0; i<3; i++) begin: gen_tmr_i
            assign inp_valid[i] = inp_valid_i;
            assign oup_ready[i] = oup_ready_i;
        end
    end

    for(genvar i=0; i<3; i++) begin: gen_tmr_join
        stream_join #(
            .N_INP(N_INP)
        ) i_join (
            .inp_valid_i(inp_valid[i]),
            .inp_ready_o(inp_ready[i]),
            .oup_valid_o(oup_valid[i]),
            .oup_ready_i(oup_ready[i])
        );
    end

  // Error reporting
  assign err_o = |faults;

endmodule