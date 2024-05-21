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

`include "voters.svh"
`include "common_cells/registers.svh"

module time_DMR_end # (
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

    // Direct connection to corresponding time_DMR_start module
    input logic [IDSize-1:0] next_id_i,

    // Upstream connection
    input DataType data_i,
    input logic [IDSize-1:0] id_i,
    input logic valid_i,
    output logic ready_o,

    // Signal for working with upstream Lockable RR Arbiter
    output logic lock_o,

    // Downstream connection
    output DataType data_o,
    output logic [IDSize-1:0] id_o,
    output logic needs_retry_o,
    output logic valid_o,
    input logic ready_i,

    // Output Flags for Error Counting
    output logic fault_detected_o
);

    // Redundant Output signals
    logic ready_ov[REP];
    logic valid_ov[REP];
    logic needs_retry_ov[REP];
    logic fault_detected_ov[REP];

    /////////////////////////////////////////////////////////////////////////////////
    // Storage of incomming results and generating good output data

    DataType data_q;
    logic [IDSize-1:0] id_q;

    // Next State Combinatorial Logic
    logic load_enable;
    assign load_enable = valid_i & ready_o & enable_i;

    // Storage Element
    `FFL(data_q, data_i, load_enable, 'h1);
    `FFL(id_q, id_i, load_enable, 'h1);

    /////////////////////////////////////////////////////////////////////////////////
    // Comparisons genereration for Handshake / State Machine

    logic [1:0] data_same, id_same, full_same, partial_same;
    logic data_same_in, id_same_in;
    logic data_same_q, id_same_q;

    always_comb begin: gen_data_same
        data_same_in = '0;
        id_same_in = '0;

        // If disabled just send out input
        if (!enable_i) begin
            data_o = data_i;
            id_o = id_i;
        end else begin
            data_o = data_q;
            id_o = id_q;
        end

        if (data_i == data_q) data_same_in = '1;
        if (id_i == id_q)  id_same_in = '1;
    end


    /////////////////////////////////////////////////////////////////////////////////
    // Storage of same / not same for one extra cycle

    `FFL(data_same_q, data_same_in, load_enable, 1'b1);
    `FFL(id_same_q, id_same_in,  load_enable, 1'b1);

    // Output (merged) signal assigment
    assign data_same = {data_same_q, data_same_in};
    assign id_same   = {id_same_q, id_same_in};

    assign full_same = data_same & id_same;
    assign partial_same = data_same | id_same;

    /////////////////////////////////////////////////////////////////////////////////
    // Logic to find out what we should do with our data based on same / not same

    logic new_element_arrived_v[REP];
    logic data_usable_v[REP];

    // Flag Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin: gen_data_flags
        always_comb begin: gen_data_flags_comb
            // Some new element just showed up and we need to send data outwards again.
            new_element_arrived_v[r] = (id_same == 2'b01) || (id_same == 2'b00);

            // Data has at least two new things that are the same
            data_usable_v[r] = data_same[0];
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to figure out handshake

    typedef enum logic [0:0] {BASE, WAIT_FOR_READY} state_t;
    state_t state_v[REP], state_d[REP], state_q[REP];
    logic valid_internal_v[REP], lock_internal_v[REP];

    // Special State Description:
    // Wait for Ready: We got some data that is usable, but downstream can't use it yet
    // -> We keep shifting as far as our pipeline goes to collect all data samples if we haven't yet and then stop
    // Wait for Valid: We got some data that is usable, and sent it downstream right away
    // -> We try to collect one more piece of our data and then move on


    // Next State Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin: gen_next_state
        always_comb begin: gen_next_state_comb
            // Default to staying in the same state
            state_v[r] = state_q[r];

            case (state_q[r])
                BASE:
                    if (valid_i) begin
                        if (new_element_arrived_v[r]) begin
                            if (!ready_i) begin
                                state_v[r] = WAIT_FOR_READY;
                            end
                        end
                    end
                WAIT_FOR_READY:
                    if (ready_i) begin
                        state_v[r] = BASE; // Downstream takes the data that we are holding and we can go back to the base state
                    end
            endcase
        end
    end

    // Generate default cases
    state_t state_b[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_default_state
        assign state_b[r] = BASE;
    end

    // State Voting Logic
    if (InternalRedundancy) begin: gen_state_voters
        `VOTE3to3ENUM(state_v, state_d);
    end else begin: gen_state_passthrough
        assign state_d = state_v;
    end

    // State Storage
    `FF(state_q, state_d, state_b);

    // Output Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin: gen_output
        always_comb begin: gen_output_comb
            if (enable_i) begin
                case (state_q[r])
                    BASE:           valid_internal_v[r] = valid_i & new_element_arrived_v[r];
                    WAIT_FOR_READY: valid_internal_v[r] = valid_i;
                endcase

                case (state_q[r])
                    BASE:           lock_internal_v[r] = !ready_i | !full_same[0];
                    WAIT_FOR_READY: lock_internal_v[r] = !ready_i;
                endcase

                case (state_q[r])
                    BASE:           ready_ov[r] = ready_i | !new_element_arrived_v[r];
                    WAIT_FOR_READY: ready_ov[r] = ready_i;
                endcase
            end else begin
                valid_internal_v[r] = valid_i;
                lock_internal_v[r] = 0;
                ready_ov[r] = ready_i;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to lock / unlock Arbitrator with Watchdog timer

    logic lock_v[REP], lock_d[REP], lock_q[REP];
    logic [$clog2(LockTimeout)-1:0] counter_v[REP], counter_d[REP], counter_q[REP];

    // Next State Combinatorial Logic
    for (genvar r = 0; r < REP; r++) begin: gen_lock_next_state
        always_comb begin: gen_lock_next_state_comb
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
    if (InternalRedundancy) begin : gen_lock_voters
        `VOTE3to3(lock_v, lock_d);
        `VOTE3to3(counter_v, counter_d);
    end else begin: gen_lock_passthrough
        assign counter_d = counter_v;
        assign lock_d = lock_v;
    end

    assign lock_o = lock_d[0];

    // Default state
    logic lock_b[REP];
    logic [$clog2(LockTimeout)-1:0] counter_b[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_lock_default_state
        assign lock_b[r] = '0;
        assign counter_b[r] = '0;
    end

    // State Storage
    `FF(lock_q, lock_d, lock_b);
    `FF(counter_q, counter_d, counter_b);

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Output deduplication based on ID and ID Faults

    logic id_fault_q;
    assign id_fault_q = ^id_q;

    logic [2 ** (IDSize-1)-1:0] recently_seen_v[REP], recently_seen_d[REP], recently_seen_q[REP];

    for (genvar r = 0; r < REP; r++) begin: gen_deduplication_next_state
        always_comb begin: gen_deduplication_next_state_comb
            recently_seen_v[r] = recently_seen_q[r];

            recently_seen_v[r][next_id_i[IDSize-2:0]] = 0;

            if (valid_internal_v[r] & ready_i & !id_fault_q) begin
                recently_seen_v[r][id_q[IDSize-2:0]] = 1;
            end
        end
    end

    // State Voting Logic
    if (InternalRedundancy) begin: gen_deduplication_voters
        `VOTE3to3(recently_seen_v, recently_seen_d);
    end else begin: gen_deduplication_passthrough
        assign recently_seen_d = recently_seen_v;
    end

    // Default state
    logic [2 ** (IDSize-1)-1:0] recently_seen_b[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_deduplication_default_state
        assign recently_seen_b[r] = ~'0; // All 1s!
    end

    // State Storage
    `FF(recently_seen_q, recently_seen_d, recently_seen_b);

    for (genvar r = 0; r < REP; r++) begin: gen_deduplication_output
        always_comb begin: gen_deduplication_output_comb
            if (enable_i) begin
                if (id_fault_q | recently_seen_q[r][id_q[IDSize-2:0]] & valid_internal_v[r]) begin
                    valid_ov[r] = 0;
                end else begin
                    valid_ov[r] = valid_internal_v[r];
                end
                needs_retry_ov[r] = id_same[0] & !data_usable_v[r];
            end else begin
                valid_ov[r] = valid_internal_v[r];
                needs_retry_ov[r] = 0;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Build error flag

    // Since we can sometimes output data that only showed up for one cycle e.g. when another id was faulty
    // or handshake failed and are sure it does not need retry, but a fault occured anyway
    // We can not us the need_retry_o signal to signify all faults. Instead we have a special signal
    // In a non-error case, we should have a full same signal every other cycle
    // So if that is not the case we had a fault.

    logic fault_detected_d[REP], fault_detected_q[REP];

    for (genvar r = 0; r < REP; r++) begin: gen_flag_next_state
        assign fault_detected_d[r] = ~|full_same[1:0] & valid_i;;
    end

    // Default state
    logic fault_detected_b[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_flag_default_state
        assign fault_detected_b[r] = '0;
    end

    `FF(fault_detected_q, fault_detected_d, fault_detected_b);

    for (genvar r = 0; r < REP; r++) begin: gen_flag_output
        assign fault_detected_ov[r] = fault_detected_d[r] & !fault_detected_q[r];
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Output Voting

    if (InternalRedundancy) begin: gen_output_voters
        `VOTE3to1(ready_ov, ready_o);
        `VOTE3to1(valid_ov, valid_o);
        `VOTE3to1(needs_retry_ov, needs_retry_o);
        `VOTE3to1(fault_detected_ov, fault_detected_o);
    end else begin: gen_output_passthrough
        assign ready_o = ready_ov[0];
        assign valid_o = valid_ov[0];
        assign needs_retry_o = needs_retry_ov[0];
        assign fault_detected_o = fault_detected_ov[0];
    end

endmodule
