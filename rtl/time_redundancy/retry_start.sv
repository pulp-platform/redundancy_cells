`include "common_cells/registers.svh"
`include "voters.svh"

module retry_start # (
    parameter type DataType  = logic,
    parameter IDSize = 1
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
    input logic [IDSize-1:0] retry_id_i,
    input logic retry_valid_i,
    output logic retry_ready_o
);

    //////////////////////////////////////////////////////////////////////
    // Register to store failed id for one cycle
    logic [IDSize-1:0] failed_id_d, failed_id_q;
    logic failed_valid_d, failed_valid_q;

    always_comb begin
        if (ready_i | retry_valid_i) begin
            failed_valid_d = retry_valid_i;
        end else begin
            failed_valid_d = failed_valid_q;
        end

        if (retry_valid_i & retry_ready_o) begin
            failed_id_d = retry_id_i;
        end else begin
            failed_id_d = failed_id_q;
        end
    end

    `FF(failed_id_q, failed_id_d, '0);
    `FF(failed_valid_q, failed_valid_d, '0);

    assign retry_ready_o = ready_i | ~failed_valid_q;

    //////////////////////////////////////////////////////////////////////
    // ID Counter with parity bit

    logic [IDSize-1:0] counter_id_d, counter_id_q;

    always_comb begin
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

    always_comb begin
        // Keep data as is as abase
        data_storage_d = data_storage_q;

        if ((failed_valid_q | valid_i) & ready_i) begin
            data_storage_d[counter_id_q[IDSize-2:0]] = data_o;
        end
    end

    `FF(data_storage_q, data_storage_d, 0);

    always_comb begin
        if (failed_valid_q & ready_i) begin
            data_o = data_storage_q[failed_id_q[IDSize-2:0]];
        end else begin
            data_o = data_i;
        end
        id_o = counter_id_q;
    end

    //////////////////////////////////////////////////////////////////////
    // Handshake assignment
    assign ready_o = ready_i & !failed_valid_q;
    assign valid_o = valid_i | failed_valid_q;

endmodule
