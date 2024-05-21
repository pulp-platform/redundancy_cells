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
    parameter int unsigned IDSize = 1,
    // This parameter chooses the implementation of the internal state machine.
    // EarlyValidEnable = 1:
    //   The state machine will return a valid output after it recieved two out of three
    //   data elements belonging together if possible e.g. no faults occur (otherwise valid in third cycle)
    //   This option slightly increases area and critical path.
    // EarlyValidEnable = 0:
    //   The sate machine will always return a valid data element after collecting all 3 parts.
    //   Internal area and critical path are reduced.
    parameter bit EarlyValidEnable = 0,
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

    // Redundant Output signals
    logic ready_ov[REP];
    logic valid_ov[REP];
    logic fault_detected_ov[REP];

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

    always_comb begin: gen_data_same
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

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to figure out handshake
    logic lock_internal_v[REP];

    if (EarlyValidEnable) begin: gen_early_valid_statemachine

        // Input signal reassignment to make state machine more readable
        logic element_needs_shift_v[REP];
        logic new_element_arrived_v[REP];
        logic element_in_input_v[REP];
        logic element_relies_on_input_v[REP];
        logic data_usable_v[REP];

        for (genvar r = 0; r < REP; r++) begin: gen_data_flags
            always_comb begin: gen_data_flags_comb
                // Some new element just showed up and we need to send data outwards again.
                new_element_arrived_v[r] = (id_same != 5'b11111) && ( // ID All same -> No element change counts. ID always needs to change!
                    (full_same & 5'b01111) == 5'b00001 ||           // 1st and 2nd element the same, other two each different from pair
                    (full_same & 5'b10111) == 5'b00010              // 1st and 3rd element the same, other two each different from pair
                );

                // Data or id is in the input -> We should consume the input for this element
                // Same data or id count as matches since we can remove an inexact pair on error and be fine
                // (Pairs where one thing matches and the other doesn't which are from a different elements can only happen with two errors)
                element_in_input_v[r] = |partial_same[1:0];

                // Second register does not contain something that is completely the same elsewhere -> We should keep shifting until it is
                element_needs_shift_v[r] = ~|full_same[2:1];

                // Data is in input and only one of the registers -> We need to take valid_i into account for valid_o
                element_relies_on_input_v[r] = |full_same[1:0] & ~full_same[2];

                // Data has at least two new things that are the same
                data_usable_v[r] = |data_same[2:0];
            end
        end

        // State Definition
        // Special State Description:
        // WAIT_FOR_READY: We got some data that is usable, but downstream can't use it yet
        // -> We keep shifting as far as our pipeline goes to collect all data samples if we haven't yet and then stop
        // WAIT_FOR_VALID: We got some data that is usable, and sent it downstream right away
        // -> We try to collect one more piece of our data and then move on
        // WAIT_FOR_DATA: We got some pieces of data that should belong together but they are not the same
        // -> We try to collect one more piece of the same data and then send it downstream
        typedef enum logic [1:0] {BASE, WAIT_FOR_READY, WAIT_FOR_VALID, WAIT_FOR_DATA} state_t;
        state_t state_v[REP], state_d[REP], state_q[REP];


        // Next State Combinatorial Logic
        for (genvar r = 0; r < REP; r++) begin: gen_next_state
            always_comb begin: gen_next_state_comb
                // Default to staying in the same state
                state_v[r] = state_q[r];

                case (state_q[r])
                    BASE:
                        if (valid_i) begin
                            if (new_element_arrived_v[r]) begin
                                if (!data_usable_v[r]) begin
                                    state_v[r] = WAIT_FOR_DATA;
                                end else begin
                                    if (ready_i) begin
                                        if (element_needs_shift_v[r]) begin
                                            // We can already send our data element, but it needs another shift to collect -> Go into special stat for this
                                            state_v[r] = WAIT_FOR_VALID;
                                        end
                                    end else begin
                                        state_v[r] = WAIT_FOR_READY;  // We keep the data until downstream is ready, only shifting as far as our registers go
                                    end
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
                    WAIT_FOR_DATA: begin
                        if (valid_i) begin
                            // We got another shift to get our redundant data completed
                            if (ready_i) begin
                                state_v[r] = BASE; // And we send it on to the next stage immediately
                            end else begin
                                state_v[r] = WAIT_FOR_READY;  // We keep the data until downstream is ready, only shifting as far as our registers go
                            end
                        end
                    end
                endcase
            end
        end

        // State Voting Logic
        if (InternalRedundancy) begin : gen_state_voters
            `VOTE3to3ENUM(state_v, state_d);
        end else begin: gen_state_passthrough
            assign state_d = state_v;
        end

        // Generate default cases
        state_t state_b[REP];
        for (genvar r = 0; r < REP; r++) begin: gen_default_state
            assign state_b[r] = WAIT_FOR_VALID;
        end

        // State Storage
        `FF(state_q, state_d, state_b);

        // Output Combinatorial Logic
        for (genvar r = 0; r < REP; r++) begin: gen_output
            always_comb begin: gen_output_comb
                if (enable_i) begin
                    case (state_q[r])
                        BASE:           valid_ov[r] = (!element_relies_on_input_v[r] | valid_i) & data_usable_v[r] & new_element_arrived_v[r];
                        WAIT_FOR_DATA:  valid_ov[r] = (!element_relies_on_input_v[r] | valid_i) & data_usable_v[r];
                        WAIT_FOR_READY: valid_ov[r] = (!element_relies_on_input_v[r] | valid_i);
                        WAIT_FOR_VALID: valid_ov[r] = 0;
                    endcase

                    case (state_q[r])
                        BASE:           lock_internal_v[r] = !ready_i | element_needs_shift_v[r] | !new_element_arrived_v[r];
                        WAIT_FOR_DATA:  lock_internal_v[r] = !ready_i | element_needs_shift_v[r];
                        WAIT_FOR_READY: lock_internal_v[r] = !ready_i;
                        WAIT_FOR_VALID: lock_internal_v[r] = !valid_i;
                    endcase

                    case (state_q[r])
                        BASE:           ready_ov[r] =  ready_i & element_in_input_v[r] | element_needs_shift_v[r] | !new_element_arrived_v[r];
                        WAIT_FOR_DATA:  ready_ov[r] =  ready_i & element_in_input_v[r] | element_needs_shift_v[r];
                        WAIT_FOR_READY: ready_ov[r] =  ready_i & element_in_input_v[r] | element_needs_shift_v[r];
                        WAIT_FOR_VALID: ready_ov[r] =  element_in_input_v[r];
                    endcase
                end else begin
                    valid_ov[r] = valid_i;
                    lock_internal_v[r] = 0;
                    ready_ov[r] = ready_i;
                end
            end
        end
    end else begin : gen_late_valid_statemachine

        // Input signal reassignment to make state machine more readable
        logic new_id_arrived_v[REP];
        logic id_in_input_v[REP];
        logic id_all_same_v[REP];
        logic id_all_cover_v[REP];
        logic data_usable_v[REP];

        for (genvar r = 0; r < REP; r++) begin: gen_data_flags
            always_comb begin: gen_data_flags_comb
                new_id_arrived_v[r] = (
                    (id_same == 5'b00111) ||
                    (id_same == 5'b00100) ||
                    (id_same == 5'b00010) ||
                    (id_same == 5'b01010)
                );

                id_in_input_v[r] = |id_same[1:0];

                id_all_same_v[r] = &id_same[2:0];
                id_all_cover_v[r] = id_same[1];

                data_usable_v[r] = |data_same[2:0];
            end
        end

        // State Definition
        // Special State Description:
        // WAIT_FOR_READY: We got some data that is usable, but downstream can't use it yet
        // -> We keep shifting as far as our pipeline goes to collect all data samples if we haven't yet and then stop
        // WAIT_FOR_VALID: We got two usable pieces of data in the last and another register
        // -> We need to wait for at least one new data element before data can be valid again
        // WAIT_FOR_VALID_X2: We have recieved three fully usable pieces of data
        // -> We need to wait for at least two new data elements before data can be valid again
        typedef enum logic [1:0] {BASE, WAIT_FOR_READY, WAIT_FOR_VALID, WAIT_FOR_VALID_X2} state_t;
        state_t state_v[REP], state_d[REP], state_q[REP];

        // Next State Combinatorial Logic
        for (genvar r = 0; r < REP; r++) begin: gen_next_state
            always_comb begin: gen_next_state_comb
                // Default to staying in the same state
                state_v[r] = state_q[r];

                case (state_q[r])
                    BASE:
                        if (valid_i) begin
                            if (new_id_arrived_v[r]) begin
                                if (ready_i) begin
                                    if (id_all_cover_v[r]) begin
                                        state_v[r] = WAIT_FOR_VALID_X2;
                                    end else begin
                                        state_v[r] = WAIT_FOR_VALID;
                                    end
                                end else begin
                                    state_v[r] = WAIT_FOR_READY;  // We keep the data until downstream is ready, only shifting as far as our registers go
                                end
                            end
                        end
                    WAIT_FOR_READY:
                        if (ready_i) begin
                            if (id_all_cover_v[r]) begin
                                state_v[r] = WAIT_FOR_VALID_X2;
                            end else begin
                                state_v[r] = WAIT_FOR_VALID;
                            end
                        end
                    WAIT_FOR_VALID: begin
                        if (valid_i) begin
                            state_v[r] = BASE;
                        end
                    end
                    WAIT_FOR_VALID_X2: begin
                        if (valid_i) begin
                            state_v[r] = WAIT_FOR_VALID;
                        end
                    end
                endcase
            end
        end

        // State Voting Logic
        if (InternalRedundancy) begin : gen_state_voters
            `VOTE3to3ENUM(state_v, state_d);
        end else begin: gen_state_passthrough
            assign state_d = state_v;
        end

        // Generate default cases
        state_t state_b[REP];
        for (genvar r = 0; r < REP; r++) begin: gen_default_state
            assign state_b[r] = WAIT_FOR_VALID;
        end

        // State Storage
        `FF(state_q, state_d, state_b);

        // Output Combinatorial Logic
        for (genvar r = 0; r < REP; r++) begin: gen_output
            always_comb begin: gen_output_comb
                if (enable_i) begin
                    case (state_q[r])
                        BASE:              valid_ov[r] = valid_i & new_id_arrived_v[r] & data_usable_v[r];
                        WAIT_FOR_READY:    valid_ov[r] = new_id_arrived_v[r] & data_usable_v[r];
                        WAIT_FOR_VALID:    valid_ov[r] = 0;
                        WAIT_FOR_VALID_X2: valid_ov[r] = 0;
                    endcase

                    case (state_q[r])
                        BASE:              lock_internal_v[r] = !(ready_i & valid_i) | !new_id_arrived_v[r] ;
                        WAIT_FOR_READY:    lock_internal_v[r] = !ready_i;
                        WAIT_FOR_VALID:    lock_internal_v[r] = 1;
                        WAIT_FOR_VALID_X2: lock_internal_v[r] = 1;
                    endcase

                    case (state_q[r])
                        BASE:              ready_ov[r] =  ready_i & id_in_input_v[r] | !new_id_arrived_v[r];
                        WAIT_FOR_READY:    ready_ov[r] =  ready_i & id_in_input_v[r];
                        WAIT_FOR_VALID:    ready_ov[r] =  1;
                        WAIT_FOR_VALID_X2: ready_ov[r] =  1;
                    endcase
                end else begin
                    valid_ov[r] = valid_i;
                    lock_internal_v[r] = 0;
                    ready_ov[r] = ready_i;
                end
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to lock / unlock Arbitrator with Watchdog timer

    logic lock_v[REP], lock_d[REP], lock_q[REP];
    logic [$clog2(LockTimeout)-1:0] counter_v[REP], counter_d[REP], counter_q[REP];

    // Next State Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin: gen_lock_next_state
        always_comb begin : gen_lock_next_state_comb
            if (counter_q[r] > LockTimeout) begin
                lock_v[r] = 0;
                counter_v[r] = 0;

            end else begin
                if (lock_q[r] & !valid_i) begin
                    counter_v[r] = counter_q[r] + 1;
                end else begin
                    counter_v[r] = 0;
                end

                // To set Lock -> 1 require previous imput to be valid, to set Lock -> 0 lock don't require anything
                if (valid_i | lock_q[r]) begin
                    lock_v[r] = lock_internal_v[r];
                end else begin
                    lock_v[r] = lock_q[r];
                end
            end
        end
    end

    // State Voting Logic
    if (InternalRedundancy) begin: gen_lock_voters
        `VOTE3to3(lock_v, lock_d);
        `VOTE3to3(counter_v, counter_d);
    end else begin: gen_lock_passthrough
        assign counter_d = counter_v;
        assign lock_d = lock_v;
    end

    assign lock_o = lock_d[0];

    // Default state
    logic lock_base[REP];
    logic [$clog2(LockTimeout)-1:0] counter_base[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_lock_default_state
        assign lock_base[r] = '0;
        assign counter_base[r] = '0;
    end

    // State Storage
    `FF(lock_q, lock_d, lock_base);
    `FF(counter_q, counter_d, counter_base);

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Build error flag

    // Since we can already output at two same elements we could have not seen an error yet,
    // so we can't rely on valid / ready to be in sync with 3 same elements!
    // Instead we use the following observation: If the data comes nicely in pairs of 3 we
    // always have at least two data elements that are the same in the first 3 elements.
    // Make output only 1 for a signly cycle even if internal pipeline is stopped

    logic fault_detected_d[REP], fault_detected_q[REP];

    for (genvar r = 0; r < REP; r++) begin: gen_flag_next_state
        assign fault_detected_d[r] = ~|full_same[2:0] & valid_i;
    end

    // Default state
    logic fault_detected_base[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_flag_default_state
        assign fault_detected_base[r] = '0;
    end

    `FF(fault_detected_q, fault_detected_d, fault_detected_base);

    for (genvar r = 0; r < REP; r++) begin: gen_flag_output
        assign fault_detected_ov[r] = fault_detected_d[r] & !fault_detected_q[r];
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Output Voting

    if (InternalRedundancy) begin : gen_output_voters
        `VOTE3to1(ready_ov, ready_o);
        `VOTE3to1(valid_ov, valid_o);
        `VOTE3to1(fault_detected_ov, fault_detected_o);
    end else begin: gen_output_passthrough
        assign ready_o = ready_ov[0];
        assign valid_o = valid_ov[0];
        assign fault_detected_o = fault_detected_ov[0];
    end

endmodule
