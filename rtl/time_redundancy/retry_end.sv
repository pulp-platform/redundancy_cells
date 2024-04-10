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
    input logic failed_ready_i,
    input logic [ID_SIZE-1:0] next_id_i
);

    /////////////////////////////////////////////////////////////////////
    // Store if data was recently already seen
    logic [2 ** ID_SIZE-1:0] good_d, good_q;

    always_comb begin
        // Keep data as is as abase
        good_d = good_q;

        good_d[next_id_i] = 0;

        if (valid_i & ready_o) begin
            good_d[id_i] = 1;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            good_q <= 16'hFFFF;
        end else begin
            good_q <= good_d;
        end
    end

    // Assign signals
    assign failed_id_o = id_i;
    assign data_o = data_i;

    logic test;
    assign test = good_q[id_i] & valid_i ;

    always_comb begin
        if (test) begin
            failed_valid_o = 0;
            valid_o = 0;
            ready_o = 1;
        end else if (faulty_i) begin
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


