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

    for (genvar r = 0; r < REP; r++) begin
        always_comb begin : next_state_logic
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
    if (InternalRedundancy) begin : gen_state_voters
        `VOTE3to3ENUM(state_v, state_d);
        `VOTE3to3(id_v, id_d);
        `VOTE3to3(data_v, data_d);
    end else begin
        assign state_d = state_v;
        assign data_d = data_v;
        assign id_d = id_v;
    end

    // Generate default cases
    state_t state_base[REP];
    DataType data_base[REP];
    logic [IDSize-1:0] id_base[REP];

    for (genvar r = 0; r < REP; r++) begin
        assign state_base[r] = STORE_AND_SEND;
        assign data_base[r] = 0;
        assign id_base[r] = 0;
    end

    // State Storage
    `FF(state_q, state_d, state_base);
    `FF(data_q, data_d, data_base);
    `FF(id_q, id_d, id_base);

    // Output Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin
        always_comb begin : output_logic
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

    if (InternalRedundancy) begin : gen_output_voters
        `VOTE3to1(ready_ov, ready_o);
        `VOTE3to1(valid_ov, valid_o);
    end else begin
        assign ready_o = ready_ov[0];
        assign valid_o = valid_ov[0];
    end

endmodule
