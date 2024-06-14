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
    parameter int unsigned IDSize = 1
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

    always_comb begin: data_same_generation_comb
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

    logic new_element_arrived;
    logic data_usable;

    // Flag Combinatorial Logic
    always_comb begin : data_flags_generation_comb
        // Some new element just showed up and we need to send data outwards again.
        new_element_arrived = (id_same == 2'b01) || (id_same == 2'b00);

        // Data has at least two new things that are the same
        data_usable = data_same[0];
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to figure out handshake

    typedef enum logic [0:0] {BASE, WAIT_FOR_READY} state_t;
    state_t state_d, state_q;
    logic valid_internal, lock_internal;

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
                        if (!ready_i) begin
                            state_d = WAIT_FOR_READY;
                        end
                    end
                end
            WAIT_FOR_READY:
                if (ready_i) begin
                    state_d = BASE; // Downstream takes the data that we are holding and we can go back to the base state
                end
        endcase
    end


    // State Storage
    `FF(state_q, state_d, BASE);

    // Output Combinatorial Logic
    always_comb begin: output_generation_comb
        if (enable_i) begin
            case (state_q)
                BASE:           valid_internal = valid_i & new_element_arrived;
                WAIT_FOR_READY: valid_internal = valid_i;
            endcase

            case (state_q)
                BASE:           lock_internal = !ready_i | !full_same[0];
                WAIT_FOR_READY: lock_internal = !ready_i;
            endcase

            case (state_q)
                BASE:           ready_o = ready_i | !new_element_arrived;
                WAIT_FOR_READY: ready_o = ready_i;
            endcase
        end else begin
            valid_internal = valid_i;
            lock_internal = 0;
            ready_o = ready_i;
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // State machine to lock / unlock Arbitrator with Watchdog timer

    logic lock_d, lock_q;
    logic [$clog2(LockTimeout)-1:0] counter_d, counter_q;
    logic lock_reset;

    // Next State Combinatorial Logic
    always_comb begin : lock_comb

        if (counter_q > LockTimeout) begin
            lock_d = 0;
            counter_d = 0;
            lock_reset = 1;

        end else begin
            lock_reset = 0;

            if (lock_q & !valid_i) begin // TODO: Add dependency on valid
                counter_d = counter_q + 1;
            end else begin
                counter_d = 0;
            end

            // To set Lock -> 1 require previous imput to be valid, to set Lock -> 0 lock don't require anything
            if (valid_i | lock_q) begin
                lock_d = lock_internal;
            end else begin
                lock_d = lock_q;
            end
        end
    end

    assign lock_o = lock_d;

    // State Storage
    `FF(lock_q, lock_d, '0);
    `FF(counter_q, counter_d, '0);

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Output deduplication based on ID and ID Faults

    logic id_fault_q;
    assign id_fault_q = ^id_q;

    logic [2 ** (IDSize-1)-1:0] recently_seen_d, recently_seen_q;

    always_comb begin
        recently_seen_d = recently_seen_q;

        recently_seen_d[next_id_i[IDSize-2:0]] = 0;

        if (valid_internal & ready_i & !id_fault_q) begin
            recently_seen_d[id_q[IDSize-2:0]] = 1;
        end
    end

    // State Storage
    `FF(recently_seen_q, recently_seen_d, ~'0);

    always_comb begin
        if (enable_i) begin
            if (id_fault_q | recently_seen_q[id_q[IDSize-2:0]] & valid_internal) begin
                valid_o = 0;
            end else begin
                valid_o = valid_internal;
            end  
            needs_retry_o = id_same[0] & !data_usable;
        end else begin
            valid_o = valid_internal;
            needs_retry_o = 0;
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////////////
    // Build error flag

    // Since we can sometimes output data that only showed up for one cycle e.g. when another id was faulty
    // or handshake failed and are sure it does not need retry, but a fault occured anyway
    // We can not us the need_retry_o signal to signify all faults. Instead we have a special signal
    // In a non-error case, we should have a full same signal every other cycle
    // So if that is not the case we had a fault.

    logic fault_detected_d, fault_detected_q;

    assign fault_detected_d = ~|full_same[1:0];

    `FF(fault_detected_q, fault_detected_d, '0);

    assign fault_detected_o = fault_detected_d & !fault_detected_q;

endmodule
