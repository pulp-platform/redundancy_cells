module retry_end # (
    parameter type DataType  = logic,
    parameter IDSize = 1
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
    output logic retry_valid_o,
    input logic retry_ready_i
);
    
    // Assign signals
    assign retry_id_o = id_i;
    assign data_o = data_i;

    always_comb begin
        if (needs_retry_i) begin
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


