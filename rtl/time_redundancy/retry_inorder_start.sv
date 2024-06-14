// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 25.04.2024
// Description: retry is a pair of modules that can be used to run an operation
// passing through a (pipelined) combinatorial process.
//
// In order to propperly function:
// - id_o of retry_start needs to be passed paralelly along the combinatorial logic,
//   using the same handshake and arrive at id_i of retry_end
// - interface retry of retry_start needs to be directly connected to retry of retry_end
// - All elements in processing have a unique ID
//
// This module always keeps results in order by also retrying results that have been correct
// but at the wronge place or time.

`include "common_cells/registers.svh"

`define INCREMENT_WITH_PARITY(input_signal, output_signal) \
begin \
    output_signal[$bits(input_signal)-2:0] = input_signal[$bits(input_signal)-2:0] + 1; \
    output_signal[$bits(input_signal)-1] = ^output_signal[$bits(input_signal)-2:0]; \
end

module retry_inorder_start # (
    parameter type DataType  = logic,
    parameter int IDSize = 1
) (
    input logic clk_i,
    input logic rst_ni,

    // Upstream connection
    input DataType data_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic [IDSize-1:0] id_o,
    output logic valid_o,
    input logic ready_i,

    // Retry Connection
    retry_interface.start retry
);

    //////////////////////////////////////////////////////////////////////
    // Register to store failed id for one cycle
    logic [IDSize-1:0] failed_id_d, failed_id_q;
    logic failed_valid_d, failed_valid_q;
    logic retry_lock_d, retry_lock_q;

    always_comb begin: gen_next_cycle_decision
        if (ready_i | retry.valid) begin
            failed_valid_d = retry.valid;
        end else begin
            failed_valid_d = failed_valid_q;
        end

        if (retry.valid & retry.ready) begin
            failed_id_d = retry.id;
        end else begin
            failed_id_d = failed_id_q;
        end
    end

    assign retry_lock_d = retry.lock;
    `FF(failed_id_q, failed_id_d, '0);
    `FF(failed_valid_q, failed_valid_d, '0);
    `FF(retry_lock_q, retry_lock_d, '0);

    assign retry.ready = ready_i | ~failed_valid_q;

    //////////////////////////////////////////////////////////////////////
    // ID Counter with parity bit

    logic [IDSize-1:0] counter_id_d, counter_id_q;

    always_comb begin: gen_id_counter
        if ((failed_valid_q | valid_i) & ready_i) begin
            `INCREMENT_WITH_PARITY(counter_id_q, counter_id_d);
        end else begin
            counter_id_d = counter_id_q;
        end
    end

    `FF(counter_id_q, counter_id_d, 0);

    //////////////////////////////////////////////////////////////////////
    // General Element storage

    logic [2 ** (IDSize-1)-1:0][$bits(DataType)-1:0] data_storage_d, data_storage_q;

    always_comb begin: gen_failed_state
        // Keep data as is as abase
        data_storage_d = data_storage_q;

        if ((failed_valid_q | valid_i) & ready_i) begin
            data_storage_d[counter_id_q[IDSize-2:0]] = data_o;
        end
    end

    `FF(data_storage_q, data_storage_d, 0);

    always_comb begin: gen_output
        if (failed_valid_q & ready_i) begin
            data_o = data_storage_q[failed_id_q[IDSize-2:0]];
        end else begin
            data_o = data_i;
        end
        id_o = counter_id_q;
        retry.id_feedback = counter_id_d;
    end

    //////////////////////////////////////////////////////////////////////
    // Handshake assignment
    assign ready_o = ready_i & !failed_valid_q & !retry_lock_q;
    assign valid_o = valid_i & !retry_lock_q | failed_valid_q;

endmodule
