`include "common_cells/registers.svh"

module retry_inorder_end # (
    parameter type DataType  = logic,
    parameter int IDSize = 1
) (
    input logic clk_i,
    input logic rst_ni,

    // Upstream connection
    input DataType data_i,
    input logic [IDSize-1:0] id_i,
    input logic needs_retry_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic valid_o,
    input logic ready_i,

    // Retry Connection
    output logic [IDSize-1:0] retry_id_o,
    input logic [IDSize-1:0] retry_id_i,
    output logic retry_valid_o,
    output logic retry_lock_o,
    input logic retry_ready_i
);
    
    // Signals do not change, only validity changes
    assign retry_id_o = id_i;
    assign data_o = data_i;

    logic [IDSize-1:0] failed_id_d, failed_id_q;
    logic retry_d, retry_q;

    always_comb begin
        if (valid_i & retry_q) begin
            failed_id_d = failed_id_q;
            retry_d = ~(failed_id_q == id_i); 
        end else if (valid_i & needs_retry_i) begin
            failed_id_d = retry_id_i;
            retry_d = 1;
        end else begin
            failed_id_d = failed_id_q;
            retry_d = retry_q;
        end
    end

    assign retry_lock_o = retry_d;

    `FF(retry_q, retry_d, '0);
    `FF(failed_id_q, failed_id_d, '0);

    always_comb begin
        if (retry_d) begin
            retry_valid_o = valid_i;
            ready_o = retry_ready_i;
            valid_o = 0;
        end else begin
            valid_o = valid_i;
            ready_o = ready_i;
            retry_valid_o = 0;
        end
    end

endmodule


