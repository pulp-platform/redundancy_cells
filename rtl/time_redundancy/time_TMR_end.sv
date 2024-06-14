`include "voters.svh"
`include "common_cells/registers.svh"

module time_TMR_end # (
    // The data type you want to send through / replicate
    parameter type DataType  = logic,
    // How long until the time_TMR module should abort listening for further copies
    // of some data when they don't show up e.g. handshake failed
    // For an in-order process you should set this to 4
    // For an out-of-order process (with RR Arbitrator) you should set it to 5
    // In case your combinatorial logic takes more than once cycle to compute an element
    // multiply by the respective number of cycles
    parameter int unsigned LockTimeout = 4,
    // The size of the ID to use as an auxilliary signal
    // For an in-order process, this can be set to 1
    // For an out of order process, it needs to be big enough so that the out-of-orderness can never
    // rearange the elements with the same id next to each other
    // As an estimate you can use log2(longest_pipeline) + 1
    // Needs to match with time_TMR_start!
    parameter int unsigned IDSize = 1
) (
    input logic clk_i,
    input logic rst_ni,
    input logic enable_i,

    // Upstream connection
    input DataType data_i,
    input logic [IDSize-1:0] id_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic valid_o,
    input logic ready_i,

    // Signal for working with Lockable RR Arbiter
    output logic lock_o,

    // Flag for External Error Counter
    output logic fault_detected_o
);
    /////////////////////////////////////////////////////////////////////////////////
    // Storage of incomming results and generating good output data

    DataType data_q1, data_q2;
    logic [IDSize-1:0] id_q1, id_q2;
    logic load_enable;
    assign load_enable = valid_i & ready_o & enable_i;

    // Storage Element
    `FFL(data_q1, data_i, load_enable, 'h1);
    `FFL(data_q2, data_q1, load_enable, 'h2);
    `FFL(id_q1, id_i, load_enable, 'h1);
    `FFL(id_q2, id_q1, load_enable, 'h2);

    /////////////////////////////////////////////////////////////////////////////////
    // Comparisons genereration for Handshake / State Machine

    logic [4:0] data_same, id_same, full_same, partial_same;
    logic [2:0] data_same_in, id_same_in;
    logic [1:0] data_same_d, data_same_q, id_same_d, id_same_q;

    always_comb begin: data_same_generation_comb
        data_same_in = '0;
        id_same_in = '0;
        data_o = '0;

        // Slot 0 and 1 are filled with the same data (slot 2 might be different)
        if (data_i == data_q1) begin
            data_o = data_i;
            data_same_in[0] = '1;
        end

        // Slot 0 and 2 are filled with the same data (slot 1 might be different)
        // This deals with cases where the second id got corrupted
        if (data_i == data_q2) begin
            data_o = data_i;
            data_same_in[1] = '1;
        end

        // Slot 1 and 2 are filled with the same data (slot 0 might be different)
        if (data_q1 == data_q2) begin
            data_o = data_q1;
            data_same_in[2] = '1;
        end

        // If disabled just send out input
        if (!enable_i) begin
            data_o = data_i;
        end

        // Same kind of logic for id signal
        if (id_i == id_q1)  id_same_in[0] = '1;
        if (id_i == id_q2)  id_same_in[1] = '1;
        if (id_q1 == id_q2) id_same_in[2] = '1;
    end

    /////////////////////////////////////////////////////////////////////////////////
    // Storage of same / not same for one extra cycle

    // Next State Combinatorial Logic
    always_comb begin : data_same_storage_comb
        data_same_d = data_same_in[2:1];
        id_same_d   = id_same_in[2:1];
    end

    // Storage Element
    `FFL(data_same_q, data_same_d, load_enable, 2'b11);
    `FFL(id_same_q, id_same_d, load_enable, 2'b11);

    // Output (merged) signal assigment
    assign data_same = {data_same_q, data_same_in};
    assign id_same   = {id_same_q, id_same_in};

    assign full_same = data_same & id_same;
    assign partial_same = data_same | id_same;

    /////////////////////////////////////////////////////////////////////////////////
    // Logic to find out what we should do with our data based on same / not same

    logic  element_needs_shift;
    logic  new_element_arrived;
    logic  element_in_input;
    logic  element_relies_on_input;
    logic  data_usable;

    // Flag Combinatorial Logic
    always_comb begin : data_flags_generation_comb
        // Some new element just showed up and we need to send data outwards again.
        new_element_arrived = (id_same != 5'b11111) && ( // ID All same -> No element change counts. ID always needs to change!
            (full_same & 5'b01111) == 5'b00001 ||           // 1st and 2nd element the same, other two each different from pair
            (full_same & 5'b10111) == 5'b00010              // 1st and 3rd element the same, other two each different from pair
        );

        // Data or id is in the input -> We should consume the input for this element
        // Same data or id count as matches since we can remove an inexact pair on error and be fine
        // (Pairs where one thing matches and the other doesn't which are from a different elements can only happen with two errors)
        element_in_input = |partial_same[1:0];

        // Second register does not contain something that is completely the same elsewhere -> We should keep shifting until it is
        element_needs_shift = ~|full_same[2:1];

        // Data is in input and only one of the registers -> We need to take valid_i into account for valid_o
        element_relies_on_input = |full_same[1:0] & ~full_same[2];

        // Data has at least two new things that are the same
        data_usable = |data_same[2:0];
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to figure out handshake

    typedef enum logic [1:0] {BASE, WAIT_FOR_READY, WAIT_FOR_VALID, WAIT_FOR_DATA} state_t;
    state_t state_d, state_q;
    logic lock;

    // Special State Description:
    // Wait for Ready: We got some data that is usable, but downstream can't use it yet
    // -> We keep shifting as far as our pipeline goes to collect all data samples if we haven't yet and then stop
    // Wait for Valid: We got some data that is usable, and sent it downstream right away
    // -> We try to collect one more piece of our data and then move on

    // Next State Combinatorial Logic
    always_comb begin : next_state_generation_comb
        // Default to staying in the same state
        state_d = state_q;

        case (state_q)
            BASE:
                if (valid_i) begin
                    if (new_element_arrived) begin
                        if (!data_usable) begin
                            state_d = WAIT_FOR_DATA;
                        end else begin
                            if (ready_i) begin
                                if (element_needs_shift) begin
                                    // We can already send our data element, but it needs another shift to collect -> Go into special stat for this
                                    state_d = WAIT_FOR_VALID;
                                end
                            end else begin
                                state_d = WAIT_FOR_READY;  // We keep the data until downstream is ready, only shifting as far as our registers go
                            end
                        end
                    end
                end
            WAIT_FOR_READY:
                if (ready_i) begin
                    state_d = BASE; // Downstream takes the data that we are holding and we can go back to the base state
                end
            WAIT_FOR_VALID: begin
                if (valid_i) begin
                    state_d = BASE; // We needed another shift to get back into base state
                end
            end
            WAIT_FOR_DATA: begin
                if (valid_i) begin
                    // We got another shift to get our redundant data completed
                    if (ready_i) begin
                        state_d = BASE; // And we send it on to the next stage immediately
                    end else begin
                        state_d = WAIT_FOR_READY;  // We keep the data until downstream is ready, only shifting as far as our registers go
                    end
                end
            end
        endcase
    end

    // State Storage
    `FF(state_q, state_d, WAIT_FOR_VALID);

    // Output Combinatorial Logic
    always_comb begin: output_generation_comb
        if (enable_i) begin
            case (state_q)
                BASE:           valid_o = (!element_relies_on_input | valid_i) & data_usable & new_element_arrived;
                WAIT_FOR_DATA:  valid_o = (!element_relies_on_input | valid_i) & data_usable;
                WAIT_FOR_READY: valid_o = (!element_relies_on_input | valid_i);
                WAIT_FOR_VALID: valid_o = 0;
            endcase

            case (state_q)
                BASE:           lock = !ready_i | element_needs_shift | !new_element_arrived;
                WAIT_FOR_DATA:  lock = !ready_i | element_needs_shift;
                WAIT_FOR_READY: lock = !ready_i;
                WAIT_FOR_VALID: lock = !valid_i;
            endcase

            case (state_q)
                BASE:           ready_o =  ready_i & element_in_input | element_needs_shift | !new_element_arrived;
                WAIT_FOR_DATA:  ready_o =  ready_i & element_in_input | element_needs_shift;
                WAIT_FOR_READY: ready_o =  ready_i & element_in_input | element_needs_shift;
                WAIT_FOR_VALID: ready_o =  element_in_input;
            endcase
        end else begin
            valid_o = valid_i;
            lock = 0;
            ready_o = ready_i;
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to lock / unlock Arbitrator with Watchdog timer

    logic lock_d, lock_q;
    logic [$clog2(LockTimeout)-1:0] counter_d, counter_q;

    // Next State Combinatorial Logic
    always_comb begin : lock_comb
        if (counter_q > LockTimeout) begin
            lock_d = 0;
            counter_d = 0;
        end else begin

            if (lock_q & !valid_i) begin // TODO: Add dependency on valid
                counter_d = counter_q + 1;
            end else begin
                counter_d = 0;
            end

            // To set Lock -> 1 require previous imput to be valid, to set Lock -> 0 lock don't require anything
            if (valid_i | lock_q) begin
                lock_d = lock;
            end else begin
                lock_d = lock_q;
            end
        end
    end

    // Output Logic
    assign lock_o = lock_d;

    // State Storage
    `FF(lock_q, lock_d, '0);
    `FF(counter_q, counter_d, '0);

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Build error flag

    // Since we can already output at two same elements we could have not seen an error yet, 
    // so we can't rely on valid / ready to be in sync with 3 same elements!
    // Instead we use the following observation: If the data comes nicely in pairs of 3 we 
    // always have at least two data elements that are the same.
    // Make output only 1 for a signly cycle even if internal pipeline is stopped

    logic fault_detected_d, fault_detected_q;

    assign fault_detected_d = ~|full_same[2:0];

    `FF(fault_detected_q, fault_detected_d, '0);

    assign fault_detected_o = fault_detected_d & !fault_detected_q;

endmodule
