// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 25.04.2024
// Description: time_DMR is a pair of modules that can be used to
// detect faults in any (pipelined) combinatorial process. This is
// done by repeating each input twice and comparing the outputs.
//
// Faults that can be handled:
// - Any number of fault in the datapath during one cycle e.g. wrong result.
// - A single fault in the handshake (valid or ready) e.g. dropped or injected results.
// - A single fault in the accompanying ID.
//
// In case a fault occurs and the result needs to be recalculated, the needs_retry_o signal
// is asserted for one cycle and the ID that needs to be tried again is given.
// Not all faults nessesarily need a retry, in case you just want to know if
// faults are happening you can use fault_detected_o for it.
//
// This needs_retry_o signal should be used to trigger some kind of mitigating action:
// For example, one could use the "retry" modules or "retry_inorder" modules
// to recalculate in hardware, or invoke some recalculation or error on the software side.
//
// In order to propperly function:
// - next_id_o of time_DMR_start needs to be directly connected to next_id_i of time_DMR_end.
// - id_o of time_DMR_start needs to be passed paralelly to the combinatorial logic, using the same handshake
//   and arrive at id_i of time_DMR_end.
// - All operation pairs in contact with each other have a unique ID.
// - The module can only be enabled / disabled when the combinatorially process holds no valid data.
//
// This module can deal with out-of-order combinatorial processes under the conditions that
// the two operations belonging together are not separated.
// To facilitate this on the output side the module has the lock_o signal which is asserted if
// the module wants another element of the same kind in the next cycle.
// This can for example be used with the rr_arb_tree_lock module, but other implementations are
// permissible.

`include "redundancy_cells/voters.svh"
`include "common_cells/registers.svh"

`define INCREMENT_WITH_PARITY(input_signal, output_signal) \
begin \
    output_signal[$bits(input_signal)-2:0] = input_signal[$bits(input_signal)-2:0] + 1; \
    output_signal[$bits(input_signal)-1] = ^output_signal[$bits(input_signal)-2:0]; \
end

module time_DMR_start # (
    // The data type you want to send through / replicate
    parameter type DataType  = logic,
    // The size of the ID to use as an auxilliary signal
    // For an in-order process, this can be set to 1
    // For an out of order process, it needs to be big enough so that the
    // out-of-orderness can never  rearange the elements with the same id
    // next to each other and needs an extra bit for error detection.
    // As an estimate you can use log2(longest_pipeline) + 2.
    // Needs to match with time_TMR_end!
    parameter int unsigned IDSize = 1,
    // Set to 1 if the id_i port should be used
    parameter bit UseExternalId = 0,
    // Determines if the internal state machines should
    // be parallely redundant, meaning errors inside this module
    // can also not cause errors in the output
    // The external output is never protected!
    parameter bit InternalRedundancy = 0,
    // Do not modify
    localparam int REP = InternalRedundancy ? 3 : 1
) (
    input logic clk_i,
    input logic rst_ni,
    input logic enable_i,

    // Direct connection
    output logic [IDSize-1:0] next_id_o,

    // Upstream connection
    input DataType data_i,
    input logic [IDSize-1:0] id_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic [IDSize-1:0] id_o,
    output logic valid_o,
    input logic ready_i
);
    // Redundant Output signals
    logic [REP-1:0][IDSize-1:0] next_id_ov;
    logic [REP-1:0] ready_ov;
    logic [REP-1:0] valid_ov;

    // State machine TLDR
    // - counting the state from 0 to 2 if the handshake is good
    // - counting the ID up whenever the state goes back to 0

    // Next State Combinatorial Logic
    typedef enum logic [1:0] {STORE_AND_SEND, SEND, REPLICATE} state_t;
    state_t [REP-1:0] state_b, state_v, state_d, state_q;
    DataType [REP-1:0] data_b, data_v, data_d, data_q;
    logic [REP-1:0][IDSize-1:0] id_b, id_v, id_d, id_q;

    for (genvar r = 0; r < REP; r++) begin: gen_next_state
        always_comb begin: gen_next_state_comb
            // Default to staying in same state
            state_v[r] = state_q[r];
            data_v[r] = data_q[r];
            id_v[r] = id_q[r];

            if (UseExternalId == 1) begin
                next_id_ov[r] = id_i;
            end else begin
                `INCREMENT_WITH_PARITY(id_q[r], next_id_ov[r]);
            end

            case (state_q[r])
                STORE_AND_SEND:
                    if (valid_i) begin
                        data_v[r] = data_i;
                        id_v[r] = next_id_ov[r];

                        if (ready_i) begin
                            if (enable_i) begin
                                state_v[r] = REPLICATE;
                            end else begin
                                state_v[r] = STORE_AND_SEND;
                            end
                        end else begin
                            state_v[r] = SEND;
                        end
                    end
                SEND:
                    if (ready_i) begin
                        if (enable_i) begin
                            state_v[r] = REPLICATE; // Reset seqeuence
                        end else begin
                            state_v[r] = STORE_AND_SEND;
                        end
                    end
                REPLICATE:
                    if (ready_i) begin
                        state_v[r] = STORE_AND_SEND;
                    end
            endcase
        end
    end

    // State Voting Logic
    `VOTEXX(REP, state_v, state_d);
    `VOTEXX(REP, id_v, id_d);
    `VOTEXX(REP, data_v, data_d);

    // Generate default cases
    for (genvar r = 0; r < REP; r++) begin: gen_default_state
        assign state_b[r] = STORE_AND_SEND;
        assign data_b[r] = 0;
        assign id_b[r] = 0;
    end

    // State Storage
    `FF(state_q, state_d, state_b);
    `FF(data_q, data_d, data_b);
    `FF(id_q, id_d, id_b);

    // Output Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin: gen_output
        always_comb begin : gen_output_comb
            case (state_q[r])
                STORE_AND_SEND: begin
                    valid_ov[r] = valid_i;
                    ready_ov[r] = 1;
                end
                SEND: begin
                    valid_ov[r] = '1;
                    ready_ov[r] = '0;
                end
                REPLICATE: begin
                    valid_ov[r] = '1;
                    ready_ov[r] = '0;
                end
            endcase
        end
    end

    // Output Voting Logic
    assign data_o = data_d[0];
    assign id_o = id_d[0];

    `VOTEX1(REP, next_id_ov, next_id_o);
    `VOTEX1(REP, ready_ov, ready_o);
    `VOTEX1(REP, valid_ov, valid_o);

endmodule
