
`define MAJORITY(a, b, c, o) \
begin \
    o = (a & b) | (a & c) | (b & c); \
end

`define BITWISE(a) \
    a[$bits(a)-1:0]

`define VOTE3to3(input_signal, output_signal) \
begin \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal[0]); \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal[1]); \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal[2]); \
end

`define VOTE3to3ENUM(input_signal, output_signal) \
begin \
    `MAJORITY(`BITWISE(input_signal[0]), `BITWISE(input_signal[1]), `BITWISE(input_signal[2]),  `BITWISE(output_signal[0])); \
    `MAJORITY(`BITWISE(input_signal[0]), `BITWISE(input_signal[1]), `BITWISE(input_signal[2]),  `BITWISE(output_signal[1])); \
    `MAJORITY(`BITWISE(input_signal[0]), `BITWISE(input_signal[1]), `BITWISE(input_signal[2]),  `BITWISE(output_signal[2])); \
end

`define VOTE3to1(input_signal, output_signal) \
begin \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal); \
end


module time_DMR_start # (
    // The data type you want to send through / replicate
    parameter type DataType  = logic,
    // The size of the ID to use as an auxilliary signal
    // For an in-order process, this can be set to 1
    // For an out of order process, it needs to be big enough so that the 
    // out-of-orderness can never  rearange the elements with the same id 
    // next to each other.
    // As an estimate you can use log2(longest_pipeline) + 1.
    // Needs to match with time_TMR_end!
    parameter ID_SIZE = 1,
    parameter UseExternalId = 0
) (
    input logic clk_i,
    input logic rst_ni,
    input logic enable_i,

    // Upstream connection
    input DataType data_i,
    input logic [ID_SIZE-1:0] id_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic [ID_SIZE-1:0] id_o,
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
    logic [2:0][ID_SIZE-1:0] id_v, id_d, id_q;

    for (genvar r = 0; r < 3; r++) begin
        always_comb begin : next_state_logic
            // Default to staying in same state
            state_v[r] = state_q[r];
            data_d[r] = data_q[r];
            id_v[r] = id_q[r];

            case (state_q[r])
                STORE_AND_SEND:
                    if (valid_i) begin
                        data_d[r] = data_i;
                        if (UseExternalId) begin
                            id_v[r] = id_i;
                        end else begin
                            id_v[r] = id_q[r] + 1;
                        end

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
    always_ff @(posedge clk_i or negedge rst_ni) begin: state_ff
        if (~rst_ni) begin
            state_q <= {STORE_AND_SEND, STORE_AND_SEND, STORE_AND_SEND};
            data_q  <= '0;
            id_q    <= '0;
        end else begin
            state_q <= state_d;
            data_q  <= data_d;
            id_q    <= id_d;
        end
    end

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
    end

endmodule



module time_DMR_end # (
    // The data type you want to send through / replicate
    parameter type DataType  = logic,
    // How long until the time_TMR module should abort listening for further copies
    // of some data when they don't show up e.g. handshake failed
    // For an in-order process you should set this to 4
    // For an out-of-order process (with RR Arbitrator) you should set it to 5
    // In case your combinatorial logic takes more than once cycle to compute an element
    // multiply by the respective number of cycles
    parameter int LockTimeout = 4,
    // The size of the ID to use as an auxilliary signal
    // For an in-order process, this can be set to 1
    // For an out of order process, it needs to be big enough so that the out-of-orderness can never
    // rearange the elements with the same id next to each other
    // As an estimate you can use log2(longest_pipeline) + 1
    // Needs to match with time_TMR_start!
    parameter ID_SIZE = 1
) (
    input logic clk_i,
    input logic rst_ni,
    input logic enable_i,

    // Upstream connection
    input DataType data_i,
    input logic [ID_SIZE-1:0] id_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic [ID_SIZE-1:0] id_o,
    output logic faulty_o,
    output logic valid_o,
    input logic ready_i,

    // Signal for working with Lockable RR Arbiter
    output logic lock_o
);  
    /////////////////////////////////////////////////////////////////////////////////
    // Storage of incomming results and generating good output data

    DataType data_d, data_q;
    logic [ID_SIZE-1:0] id_d, id_q;

    // Next State Combinatorial Logic
    always_comb begin : data_storage_comb
        if (valid_i & ready_o & enable_i) begin
            data_d = data_i; 
            id_d   = id_i; 
        end else begin
            data_d = data_q; 
            id_d   = id_q; 
        end
    end

    // Storage Element
    always_ff @(posedge clk_i or negedge rst_ni) begin: data_storage_ff
        if (~rst_ni) begin
            data_q <= 'h1;
            id_q   <= 'h1;
        end else begin
            data_q <= data_d;
            id_q   <= id_d;
        end
    end

    // Output Combinatorial Logic (and flag genereration for handshake)
    logic [2:0][1:0] data_same, id_same, full_same, partial_same;
    logic [2:0] data_same_in, id_same_in;
    logic [2:0] data_same_d, data_same_q, id_same_d, id_same_q;
    logic [2:0][$bits(DataType)-1:0] data_ov;
    logic [2:0][ID_SIZE-1:0] id_ov;

    for (genvar r = 0; r < 3; r++) begin
        always_comb begin: data_same_generation_comb
            data_same_in[r] = '0;
            id_same_in[r] = '0;

                        // If disabled just send out input
            if (!enable_i) begin
                data_ov[r] = data_i;
                id_ov[r] = id_i;
            end else begin
                data_ov[r] = data_q;
                id_ov[r] = id_q;
            end

            if (data_i == data_q) data_same_in[r] = '1;
            if (id_i == id_q)  id_same_in[r] = '1;
        end
    end

    // Output Voting Logic
    always_comb begin : data_voting_logic
        `VOTE3to1(data_ov, data_o);
        `VOTE3to1(id_ov, id_o);
    end

    /////////////////////////////////////////////////////////////////////////////////
    // Storage of same / not same for one extra cycle

    // Next State Combinatorial Logic
    for (genvar r = 0; r < 3; r++) begin
        always_comb begin : data_same_storage_comb
            if (valid_i & ready_o & enable_i) begin
                data_same_d[r] = data_same_in[r]; 
                id_same_d[r]   = id_same_in[r]; 
            end else begin
                data_same_d[r] = data_same_q[r]; 
                id_same_d[r]   = id_same_q[r]; 
            end
        end
    end

    // Storage Element
    always_ff @(posedge clk_i or negedge rst_ni) begin: data_same_storage_ff
        if (~rst_ni) begin
            data_same_q <= {1'b1, 1'b1, 1'b1};
            id_same_q   <= {1'b1, 1'b1, 1'b1};
        end else begin
            data_same_q <= data_same_d;
            id_same_q   <= id_same_d;
        end
    end

    // Output (merged) signal assigment
    for (genvar r = 0; r < 3; r++) begin
        assign data_same[r] = {data_same_q[r], data_same_in[r]};
        assign id_same[r]   = {id_same_q[r], id_same_in[r]};
    end

    assign full_same = data_same & id_same;
    assign partial_same = data_same | id_same;

    /////////////////////////////////////////////////////////////////////////////////
    // Logic to find out what we should do with our data based on same / not same

    logic [2:0] new_element_arrived;
    logic [2:0] data_usable;

    // Flag Combinatorial Logic
    for (genvar r = 0; r < 3; r++) begin
        always_comb begin : data_flags_generation_comb
            // Some new element just showed up and we need to send data outwards again.
            new_element_arrived[r] = (id_same[r] == 2'b01) || (id_same[r] == 2'b00);

            // Data has at least two new things that are the same
            data_usable[r] = data_same[r][0];
        end
    end


    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to figure out handshake

    typedef enum logic [1:0] {BASE, WAIT_FOR_READY, WAIT_FOR_VALID} state_t;
    state_t state_v[3], state_d[3], state_q[3];
    logic [2:0] ready_ov, valid_ov, lock, faulty_ov;

    // Special State Description:
    // Wait for Ready: We got some data that is usable, but downstream can't use it yet
    // -> We keep shifting as far as our pipeline goes to collect all data samples if we haven't yet and then stop
    // Wait for Valid: We got some data that is usable, and sent it downstream right away
    // -> We try to collect one more piece of our data and then move on


    // Next State Combinatorial Logic
    for (genvar r = 0; r < 3; r++) begin
        always_comb begin : next_state_generation_comb
            // Default to staying in the same state
            state_v[r] = state_q[r];

            case (state_q[r])
                BASE:
                    if (valid_i) begin
                        if (new_element_arrived[r]) begin 
                            if (ready_i) begin
                                state_v[r] = WAIT_FOR_VALID;
                            end else begin 
                                state_v[r] = WAIT_FOR_READY;
                            end
                        end 
                    end
                WAIT_FOR_READY:
                    if (ready_i) begin
                        state_v[r] = BASE; // Downstream takes the data that we are holding and we can go back to the base state
                    end 
                WAIT_FOR_VALID: begin
                    if (valid_i) begin 
                        state_v[r] = BASE; // We needed another shift to get back into base state
                    end 
                end
            endcase
        end
    end

    // Next State Voting Logic
    always_comb begin : voting_logic
        `VOTE3to3ENUM(state_v, state_d);
    end

    // State Storage
    always_ff @(posedge clk_i or negedge rst_ni) begin : state_storage_ff
        if(~rst_ni) begin
             state_q <= {WAIT_FOR_VALID, WAIT_FOR_VALID, WAIT_FOR_VALID};
        end else begin
             state_q <= state_d;
        end
    end 

    // Output Combinatorial Logic
    for (genvar r = 0; r < 3; r++) begin
        always_comb begin: output_generation_comb
            if (enable_i) begin
                case (state_q[r])
                    BASE:           valid_ov[r] = valid_i & new_element_arrived[r];
                    WAIT_FOR_READY: valid_ov[r] = valid_i;
                    WAIT_FOR_VALID: valid_ov[r] = 0;
                endcase

                case (state_q[r])
                    BASE:           lock[r] = !ready_i | !full_same[r][0];
                    WAIT_FOR_READY: lock[r] = !ready_i;
                    WAIT_FOR_VALID: lock[r] = !valid_i;
                endcase

                case (state_q[r])
                    BASE:           ready_ov[r] =  ready_i | !new_element_arrived[r];
                    WAIT_FOR_READY: ready_ov[r] =  ready_i;
                    WAIT_FOR_VALID: ready_ov[r] = !valid_i;
                endcase

                faulty_ov[r] = id_same[r][0] & !data_usable[r];

            end else begin
                valid_ov[r] = valid_i;
                lock[r] = 0;
                faulty_ov[r] = 0;
                ready_ov[r] = ready_i;
            end
        end
    end

    // Output Voting Logic
    always_comb begin: output_voters
        `VOTE3to1(ready_ov, ready_o);
        `VOTE3to1(valid_ov, valid_o);
        `VOTE3to1(faulty_ov, faulty_o);
    end


    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to lock / unlock arbitrator with Watchdog timer

    logic [2:0] lock_v, lock_d, lock_q;
    logic [2:0][$clog2(LockTimeout)-1:0] counter_v, counter_d, counter_q;

    // Next State Combinatorial Logic
    for (genvar r = 0; r < 3; r++) begin
        always_comb begin : lock_comb
            if (counter_q[r] > LockTimeout) begin
                lock_v[r] = 0;
                counter_v[r] = 0;
            end else begin

                if (lock_q[r] & !valid_i) begin // TODO: Add dependency on valid
                    counter_v[r] = counter_q[r] + 1;
                end else begin
                    counter_v[r] = 0;
                end

                // To set Lock -> 1 require previous imput to be valid, to set Lock -> 0 lock don't require anything
                if (valid_i | lock_q[r]) begin
                    lock_v[r] = lock[r];
                end else begin
                    lock_v[r] = lock_q[r];
                end
            end
        end
    end

    // Next State Voting Logic / Output Voting Logic
    always_comb begin : lockoting_logic
        `VOTE3to3(lock_v, lock_d);
        `VOTE3to1(lock_v, lock_o);
        `VOTE3to3(counter_v, counter_d);
    end

    // State Storage
    always_ff @(posedge clk_i or negedge rst_ni) begin : lock_ff
        if(~rst_ni) begin
             lock_q <= '0;
             counter_q <= '0;
        end else begin
             lock_q <= lock_d;
             counter_q <= counter_d;
        end
    end 
endmodule
