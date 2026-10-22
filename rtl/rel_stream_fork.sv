// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//
// TMR-protected stream fork, with triple-modular redundancy (TMR) on FSM states,
// configurable handshakes, voting schemes, and real-time fault detection/reporting.

(* no_ungroup *)
(* no_boundary_optimization *)
module rel_stream_fork #(
    parameter int unsigned N_OUP        = 0,        // Number of outputs
    parameter bit          TmrHandshake = 1'b1,     // Use TMR for handshake signals
    parameter bit          TmrVoting    = 1'b1,     // 0=single voted state, 1=voted state per copy
    parameter int unsigned VoterType    = 1,        // 0=Classical_MV, 1=KP_MV
    parameter int unsigned HsWidth      = TmrHandshake ? 3 : 1 // width of the handshake signals
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  logic            [HsWidth-1:0] valid_i,
    output logic            [HsWidth-1:0] ready_o,
    output logic [N_OUP-1:0][HsWidth-1:0] valid_o,
    input  logic [N_OUP-1:0][HsWidth-1:0] ready_i,
    output logic                          err_o
);

    // Type definitions for FSM states
    typedef enum logic {READY, WAIT} state_t;

    // Calculate required bits for sequential state
    localparam int unsigned InpStateBits = $bits(state_t);
    localparam int unsigned OupStateBits = $bits(state_t);
    localparam int unsigned SeqStateBits       = InpStateBits + (N_OUP * OupStateBits);

    // State registers, next-state, and voted state signals
    logic [SeqStateBits-1:0] all_seq_d[3];
    logic [SeqStateBits-1:0] all_seq_q[3];
    logic [SeqStateBits-1:0] voter_q  [3];

    // Fault detection signals
    logic [2:0] seq_err;
    logic [N_OUP:0] handshake_fault;

    // Reset value for sequential state
    logic [SeqStateBits-1:0] all_seq_rst;
    assign all_seq_rst = {state_t'(READY), {N_OUP{state_t'(READY)}}};

    // FSM State Variables
    state_t inp_state_d[3], inp_state_q[3];
    state_t oup_state_d[3][N_OUP], oup_state_q[3][N_OUP];

    // Combinational handshake signals per copy
    logic [2:0]            ready_out_single;
    logic [N_OUP-1:0][2:0] valid_out_single;

    // Internal Handshake Preparation
    logic [2:0]            valid_in;
    logic [N_OUP-1:0][2:0] ready_in;

    if (TmrHandshake) begin : gen_tmr_handshake
        assign valid_in = valid_i[2:0];
        for (genvar i = 0; i < N_OUP; i++) begin : gen_ready_in
            assign ready_in[i] = ready_i[i][2:0];
        end
    end else begin : gen_non_tmr_handshake
        assign valid_in = {3{valid_i[0]}};
        for (genvar i = 0; i < N_OUP; i++) begin : gen_ready_in
            assign ready_in[i] = {3{ready_i[i][0]}};
        end
    end

    // --- FSM Logic per Copy (same FSMs as common_cells stream_fork) ---
    for (genvar copy = 0; copy < 3; copy++) begin : gen_fsm
        logic [N_OUP-1:0] oup_ready, all_ones;
        logic [N_OUP-1:0] valid_out_c, ready_in_c;
        logic             ready_out_c;

        assign all_ones = '1;
        assign ready_out_single[copy] = ready_out_c;
        for (genvar i = 0; i < N_OUP; i++) begin : gen_oup_map
            assign ready_in_c[i]             = ready_in[i][copy];
            assign valid_out_single[i][copy] = valid_out_c[i];
        end

        // Input control FSM
        always_comb begin
            inp_state_d[copy] = inp_state_q[copy];

            unique case (inp_state_q[copy])
                READY: begin
                    if (valid_in[copy]) begin
                        if (valid_out_c == all_ones && ready_in_c == all_ones) begin
                            ready_out_c = 1'b1;
                        end else begin
                            ready_out_c = 1'b0;
                            inp_state_d[copy] = WAIT;
                        end
                    end else begin
                        ready_out_c = 1'b0;
                    end
                end
                WAIT: begin
                    if (valid_in[copy] && oup_ready == all_ones) begin
                        ready_out_c = 1'b1;
                        inp_state_d[copy] = READY;
                    end else begin
                        ready_out_c = 1'b0;
                    end
                end
                default: begin
                    inp_state_d[copy] = READY;
                    ready_out_c = 1'b0;
                end
            endcase
        end

        // Output control FSMs
        for (genvar i = 0; i < N_OUP; i++) begin : gen_oup_state
            always_comb begin
                oup_ready[i]         = 1'b1;
                valid_out_c[i]       = 1'b0;
                oup_state_d[copy][i] = oup_state_q[copy][i];

                unique case (oup_state_q[copy][i])
                    READY: begin
                        if (valid_in[copy]) begin
                            valid_out_c[i] = 1'b1;
                            if (ready_in_c[i]) begin
                                if (!ready_out_c) begin
                                    oup_state_d[copy][i] = WAIT;
                                end
                            end else begin
                                oup_ready[i] = 1'b0;
                            end
                        end
                    end
                    WAIT: begin
                        if (valid_in[copy] && ready_out_c) begin
                            oup_state_d[copy][i] = READY;
                        end
                    end
                    default: begin
                        oup_state_d[copy][i] = READY;
                    end
                endcase
            end
        end
    end

    for (genvar copy = 0; copy < 3; copy++) begin : gen_tmr
        // Pack combinational next-state vector
        assign all_seq_d[copy][InpStateBits-1:0] = inp_state_d[copy];
        for (genvar i = 0; i < N_OUP; i++) begin : gen_pack_d
            assign all_seq_d[copy][InpStateBits + i*OupStateBits] = oup_state_d[copy][i];
        end

        // Sequential State Registers (Direct next-state loading)
        always_ff @(posedge clk_i or negedge rst_ni) begin : seq_block
            if (!rst_ni) begin
                all_seq_q[copy] <= all_seq_rst;
            end else begin
                all_seq_q[copy] <= all_seq_d[copy];
            end
        end
    end

    // --- Post-Register TMR Voting & State Unpacking ---
    if (TmrVoting == 1'b0) begin : gen_single_voter
        // Single shared voter driving all 3 copies
        bitwise_TMR_voter_fail #(
            .DataWidth(SeqStateBits),
            .VoterType(VoterType)
        ) i_seq_vote (
            .a_i              (all_seq_q[0]),
            .b_i              (all_seq_q[1]),
            .c_i              (all_seq_q[2]),
            .majority_o       (voter_q[0]),
            .fault_detected_o (seq_err[0])
        );

        assign voter_q[1]  = voter_q[0];
        assign voter_q[2]  = voter_q[0];
        assign seq_err[1]  = seq_err[0];
        assign seq_err[2]  = seq_err[0];
    end else begin : gen_voter_per_copy
        // Independent voters per copy
        for (genvar copy = 0; copy < 3; copy++) begin : gen_voter
            bitwise_TMR_voter_fail #(
                .DataWidth(SeqStateBits),
                .VoterType(VoterType)
            ) i_seq_vote (
                .a_i              (all_seq_q[0]),
                .b_i              (all_seq_q[1]),
                .c_i              (all_seq_q[2]),
                .majority_o       (voter_q[copy]),
                .fault_detected_o (seq_err[copy])
            );
        end
    end

    // Unpack voted state vectors into FSM current-state logic
    for (genvar copy = 0; copy < 3; copy++) begin : gen_unpack_voter
        assign inp_state_q[copy] = state_t'(voter_q[copy][InpStateBits-1:0]);
        for (genvar i = 0; i < N_OUP; i++) begin : gen_unpack_oup
            assign oup_state_q[copy][i] = state_t'(voter_q[copy][InpStateBits+i*OupStateBits]);
        end
    end

    // --- Output Handshake Assignments ---
    if (TmrHandshake) begin : gen_tmr_handshake_output
        assign ready_o = ready_out_single;
        for (genvar i = 0; i < N_OUP; i++) begin : gen_valid_o
            assign valid_o[i] = valid_out_single[i];
        end
        assign handshake_fault = '0;
    end else begin : gen_non_tmr_handshake_output
        for (genvar i = 0; i < N_OUP; i++) begin : gen_valid_o
            TMR_voter_fail #(
                .VoterType(VoterType)
            ) i_valid_tmr (
                .a_i              (valid_out_single[i][0]),
                .b_i              (valid_out_single[i][1]),
                .c_i              (valid_out_single[i][2]),
                .majority_o       (valid_o[i][0]),
                .fault_detected_o (handshake_fault[i])
            );
        end

        TMR_voter_fail #(
            .VoterType(VoterType)
        ) i_ready_tmr (
            .a_i              (ready_out_single[0]),
            .b_i              (ready_out_single[1]),
            .c_i              (ready_out_single[2]),
            .majority_o       (ready_o[0]),
            .fault_detected_o (handshake_fault[N_OUP])
        );
    end

    // Error Reporting
    assign err_o = |seq_err | |handshake_fault;

endmodule

