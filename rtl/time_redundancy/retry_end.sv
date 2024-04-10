module retry_end # (
    parameter type DataType  = logic,
    parameter ID_SIZE = 1
) (
    input logic clk_i,
    input logic rst_ni,

    // Upstream connection
    input DataType data_i,
    input logic [ID_SIZE-1:0] id_i,
    input logic faulty_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic valid_o,
    input logic ready_i,

    // Retry Connection
    output logic [ID_SIZE-1:0] failed_id_o,
    output logic failed_valid_o,
    input logic failed_ready_i
);
    
    // Assign signals
    assign failed_id_o = id_i;
    assign data_o = data_i;

    always_comb begin
        if (faulty_i) begin
            failed_valid_o = valid_i;
            ready_o = failed_ready_i;
            valid_o = 0;
        end else begin
            valid_o = valid_i;
            ready_o = ready_i;
            failed_valid_o = 0;
        end
    end

endmodule


