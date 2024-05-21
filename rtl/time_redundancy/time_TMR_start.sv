// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 25.04.2024
// Description: time_TMR is a pair of modules that can be used to error correct
// any transient fault in a (pipelined) combinatorial process. This is done by
// repeating the element three times and comparing the results
//
// Faults that can be handled:
// - Any number of fault in the datapath during one cycle e.g. wrong result.
// - A single fault in the handshake (valid or ready) e.g. dropped or injected results.
// - A single fault in the accompanying ID.
//
// In order to propperly function:
// - id_o of time_TMR_start needs to be passed paralelly to the combinatorial logic,
//   using the same handshake and arrive at id_i of time_TMR_end.
// - All operation tripplets in contact which each other have a unique ID.
// - The module can only be enabled / disabled when the combinatorially process holds no valid data.
//
// This module can deal with out-of-order combinatorial processes under the conditions that
// the three operations belonging together are not separated.
// To facilitate that the tripples stay together, the module has the lock_o signal
// Which defines if the same pipeline should output again in the next cycle.
// This can for example be used with the rr_arb_tree_lock module, but other implementations are
// permissible.

`include "voters.svh"
`include "common_cells/registers.svh"

module time_TMR_start # (
    // The data type you want to send through / replicate
    parameter type DataType  = logic,
    // The size of the ID to use as an auxilliary signal
    // For an in-order process, this can be set to 1
    // For an out of order process, it needs to be big enough so that the
    // out-of-orderness can never  rearange the elements with the same id
    // next to each other.
    // As an estimate you can use log2(longest_pipeline) + 1.
    // Needs to match with time_TMR_end!
    parameter int unsigned IDSize = 1,
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

    // Upstream connection
    input DataType data_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic [IDSize-1:0] id_o,
    output logic valid_o,
    input logic ready_i
);
    // Redundant Output signals
    logic ready_ov[REP];
    logic valid_ov[REP];

    // State machine TLDR
    // - counting the state from 0 to 2 if the handshake is good
    // - counting the ID up whenever the state goes back to 0

    // Next State Combinatorial Logic
    typedef enum logic [1:0] {STORE_AND_SEND, SEND, REPLICATE_ONE, REPLICATE_TWO} state_t;
    state_t state_v[REP], state_d[REP], state_q[REP];
    DataType  data_v[REP], data_d[REP], data_q[REP];
    logic [IDSize-1:0] id_v[REP], id_d[REP], id_q[REP];

    for (genvar r = 0; r < REP; r++) begin: gen_next_state
        always_comb begin : gen_next_state_comb
            // Default to staying in same state
            state_v[r] = state_q[r];
            data_v[r] = data_q[r];
            id_v[r] = id_q[r];

            case (state_q[r])
                STORE_AND_SEND:
                    if (valid_i) begin
                        data_v[r] = data_i;
                        id_v[r] = id_q[r] + 1;

                        if (ready_i) begin
                            if (enable_i) begin
                                state_v[r] = REPLICATE_ONE;
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
                            state_v[r] = REPLICATE_ONE; // Reset seqeuence
                        end else begin
                            state_v[r] = STORE_AND_SEND;
                        end
                    end
                REPLICATE_ONE:
                    if (ready_i) begin
                        state_v[r] = REPLICATE_TWO; // Reset seqeuence
                    end
                REPLICATE_TWO: begin
                    if (ready_i) begin
                        state_v[r] = STORE_AND_SEND;
                    end
                end
            endcase
        end
    end

    // State Voting Logic
    if (InternalRedundancy) begin: gen_state_voters
        `VOTE3to3ENUM(state_v, state_d);
        `VOTE3to3(id_v, id_d);
        `VOTE3to3(data_v, data_d);
    end else begin: gen_state_passthrough
        assign state_d = state_v;
        assign data_d = data_v;
        assign id_d = id_v;
    end

    // Generate default cases
    state_t state_b[REP];
    DataType data_b[REP];
    logic [IDSize-1:0] id_b[REP];

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
        always_comb begin: gen_output_comb
            case (state_q[r])
                STORE_AND_SEND: begin
                    valid_ov[r] = valid_i;
                    ready_ov[r] = 1;
                end
                SEND: begin
                    valid_ov[r] = '1;
                    ready_ov[r] = '0;
                end
                REPLICATE_ONE: begin
                    valid_ov[r] = '1;
                    ready_ov[r] = '0;
                end
                REPLICATE_TWO: begin
                    valid_ov[r] = '1;
                    ready_ov[r] = '0;
                end
            endcase
        end
    end

    // Output Voting Logic
    assign data_o = data_d[0];
    assign id_o = id_d[0];

    if (InternalRedundancy) begin: gen_output_voters
        `VOTE3to1(ready_ov, ready_o);
        `VOTE3to1(valid_ov, valid_o);
    end else begin: gen_output_voters
        assign ready_o = ready_ov[0];
        assign valid_o = valid_ov[0];
    end

endmodule
