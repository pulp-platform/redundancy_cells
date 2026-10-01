// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

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
    output logic [1:0]                    err_o     // [0]: correctable, [1]: uncorrectable
);

    // Type definitions for FSM states
    typedef enum logic {READY, WAIT} state_t;

    // Calculate required bits for sequential state
    localparam int unsigned INP_STATE_BITS = $bits(state_t);
    localparam int unsigned OUP_STATE_BITS = $bits(state_t);
    localparam int unsigned SEQ_BITS       = INP_STATE_BITS + (N_OUP * OUP_STATE_BITS);

    // State registers, next-state, and voted state signals
    logic [SEQ_BITS-1:0] all_seq_d[2:0];
    logic [SEQ_BITS-1:0] all_seq_q[2:0];
    logic [SEQ_BITS-1:0] voter_q  [2:0];

    // Fault detection signals
    logic [2:0] seq_err;
    logic [2:0] handshake_fault;

    // Reset value for sequential state
    logic [SEQ_BITS-1:0] all_seq_rst;
    assign all_seq_rst = {state_t'(READY), {N_OUP{state_t'(READY)}}};

    // FSM State Variables
    state_t inp_state_d[2:0], inp_state_q[2:0];
    state_t oup_state_d[2:0][N_OUP-1:0], oup_state_q[2:0][N_OUP-1:0];

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

    // --- FSM Logic & Packaging per Copy ---
    always_comb begin : gen_fsm_copy
        // Combinational Input Control FSM
        for (int copy = 0; copy < 3; copy++) begin
            logic all_outputs_hs;

            inp_state_d[copy]     = inp_state_q[copy];
            ready_out_single[copy] = 1'b0;

            // Check completion for all downstream channels
            all_outputs_hs = 1'b1;
            for (int i = 0; i < N_OUP; i++) begin
                valid_out_single[i][copy] = 1'b0;
                oup_state_d[copy][i]      = oup_state_q[copy][i];
                if (oup_state_q[copy][i] == READY) begin
                    valid_out_single[i][copy] = valid_in[copy];
                    if (valid_in[copy] && ready_in[i][copy]) begin
                        oup_state_d[copy][i] = WAIT;
                    end else begin
                        all_outputs_hs = 1'b0;
                    end
                end else begin
                    valid_out_single[i][copy] = 1'b0;
                end
            end

            // Process upstream stream readiness
            if (valid_in[copy] && all_outputs_hs) begin
                ready_out_single[copy] = 1'b1;
                inp_state_d[copy]      = READY;
                for (int i = 0; i < N_OUP; i++) begin
                    oup_state_d[copy][i] = READY;
                end
            end else if (valid_in[copy]) begin
                inp_state_d[copy] = WAIT;
            end
        end
    end
    for (genvar copy = 0; copy < 3; copy++) begin
        // Pack combinational next-state vector
        assign all_seq_d[copy][INP_STATE_BITS-1:0] = inp_state_d[copy];
        for (genvar i = 0; i < N_OUP; i++) begin : gen_pack_d
            assign all_seq_d[copy][INP_STATE_BITS + i*OUP_STATE_BITS] = oup_state_d[copy][i];
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
            .DataWidth(SEQ_BITS),
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
                .DataWidth(SEQ_BITS),
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
        assign inp_state_q[copy] = state_t'(voter_q[copy][INP_STATE_BITS-1:0]);
        for (genvar i = 0; i < N_OUP; i++) begin : gen_unpack_oup
            assign oup_state_q[copy][i] = state_t'(voter_q[copy][INP_STATE_BITS + i*OUP_STATE_BITS]);
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
    assign err_o[0] = |seq_err | |handshake_fault;
    assign err_o[1] = 1'b0;

endmodule