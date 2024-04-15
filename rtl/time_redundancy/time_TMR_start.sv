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
    parameter int unsigned IDSize = 1
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

    // State machine TLDR
    // - counting the state from 0 to 2 if the handshake is good
    // - counting the ID up whenever the state goes back to 0

    // Next State Combinatorial Logic
    typedef enum logic [1:0] {STORE_AND_SEND, SEND, REPLICATE_ONE, REPLICATE_TWO} state_t;
    state_t state_d, state_q;
    DataType  data_d, data_q;
    logic [IDSize-1:0] id_d, id_q;

    always_comb begin : next_state_logic
        // Default to staying in same state
        state_d = state_q;
        data_d = data_q;
        id_d = id_q;

        case (state_q)
            STORE_AND_SEND:
                if (valid_i) begin
                    data_d = data_i;
                    id_d = id_q + 1;

                    if (ready_i) begin
                        if (enable_i) begin
                        state_d = REPLICATE_ONE;
                        end else begin
                            state_d = STORE_AND_SEND;
                        end
                    end else begin
                        state_d = SEND;
                    end
                end
            SEND:
                if (ready_i) begin
                    if (enable_i) begin
                        state_d = REPLICATE_ONE; // Reset seqeuence
                    end else begin
                        state_d = STORE_AND_SEND;
                    end
                end
            REPLICATE_ONE:
                if (ready_i) begin
                    state_d = REPLICATE_TWO; // Reset seqeuence
                end
            REPLICATE_TWO: begin
                if (ready_i) begin
                    state_d = STORE_AND_SEND;
                end
            end
        endcase
    end

    // State Storage
    `FF(state_q, state_d, STORE_AND_SEND);
    `FF(data_q, data_d, '0);
    `FF(id_q, id_d, '0);

    // Output Combinatorial Logic
    always_comb begin : output_logic
        case (state_q)
            STORE_AND_SEND: begin
                valid_o = valid_i;
                ready_o = 1;
            end
            SEND: begin
                valid_o = '1;
                ready_o = '0;
            end
            REPLICATE_ONE: begin
                valid_o = '1;
                ready_o = '0;
            end
            REPLICATE_TWO: begin
                valid_o = '1;
                ready_o = '0;
            end
        endcase
    end

    // Output Voting Logic
    assign data_o = data_d;
    assign id_o = id_d;

endmodule
