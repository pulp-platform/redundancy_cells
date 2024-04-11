`include "voters.svh"
`include "common_cells/registers.svh"

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
    parameter IDSize = 1,
    // Set to 1 if the id_i port should be used
    parameter UseExternalId = 0
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

    // State machine TLDR
    // - counting the state from 0 to 2 if the handshake is good
    // - counting the ID up whenever the state goes back to 0

    // Next State Combinatorial Logic
    typedef enum logic [1:0] {STORE_AND_SEND, SEND, REPLICATE} state_t;
    state_t state_v[3], state_d[3], state_q[3];
    DataType [2:0] data_d, data_q;
    logic [2:0][IDSize-1:0] id_v, id_d, id_q, id_next;
    logic [2:0][IDSize-2:0] id_next_noparity;

    for (genvar r = 0; r < 3; r++) begin
        always_comb begin : next_state_logic
            // Default to staying in same state
            state_v[r] = state_q[r];
            data_d[r] = data_q[r];
            id_v[r] = id_q[r];

            id_next_noparity[r] =  id_q[r][IDSize-2:0] + 1;
            if (UseExternalId) begin
                id_next[r] = id_i;
            end else begin
                id_next[r] = {^id_next_noparity[r], id_next_noparity[r]};
            end

            case (state_q[r])
                STORE_AND_SEND:
                    if (valid_i) begin
                        data_d[r] = data_i;
                        id_v[r] = id_next[r];
        
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

    // Next State Voting Logic
    always_comb begin : voting_logic
        `VOTE3to3ENUM(state_v, state_d);
        `VOTE3to3(id_v, id_d);
    end

    // State Storage
    `FF(state_q, state_d, {STORE_AND_SEND, STORE_AND_SEND, STORE_AND_SEND});
    `FF(data_q, data_d, '0);
    `FF(id_q, id_d, '0);

    // Output Combinatorial Logic
    always_comb begin : output_logic
        case (state_q[0])
            STORE_AND_SEND: begin
                valid_o = valid_i;
                ready_o = 1;
            end
            SEND: begin
                valid_o = '1;
                ready_o = '0;
            end
            REPLICATE: begin
                valid_o = '1;
                ready_o = '0;
            end
        endcase
    end

    // Output Voting Logic
    always_comb begin: output_voters
        `VOTE3to1(data_d, data_o);
        `VOTE3to1(id_v, id_o);
        `VOTE3to1(id_next, next_id_o);
    end

endmodule
