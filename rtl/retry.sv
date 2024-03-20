module retry_start # (
    parameter type DataType  = logic,
    parameter ID_SIZE = 1
) (
    input logic clk_i,
    input logic rst_ni,

    // Upstream connection
    input DataType data_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic [ID_SIZE-1:0] id_o,
    output logic valid_o,
    input logic ready_i,

    // Retry Connection
    input logic [ID_SIZE-1:0] failed_id_i,
    input logic failed_valid_i,
    output logic failed_ready_o
);  

    //////////////////////////////////////////////////////////////////////
    // Register to store failed id for one cycle
    logic [ID_SIZE-1:0] failed_id_d, failed_id_q;
    logic failed_valid_d, failed_valid_q;

    always_comb begin

        if (ready_i | failed_valid_i) begin
            failed_valid_d = failed_valid_i;
        end else begin
            failed_valid_d = failed_valid_q;
        end

        if (failed_valid_i & failed_ready_o) begin
            failed_id_d = failed_id_i;
        end else begin
            failed_id_d = failed_id_q;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            failed_id_q <= 0;
            failed_valid_q <= 0;
        end else begin
            failed_id_q <= failed_id_d;
            failed_valid_q <= failed_valid_d;
        end
    end

    assign failed_ready_o = ready_i | ~failed_valid_q;

    //////////////////////////////////////////////////////////////////////
    // ID Counter
    logic [ID_SIZE-1:0] counter_id_d, counter_id_q;

    always_comb begin // TODO: Only count on valid?
        if ((failed_valid_q | valid_i) & ready_i) begin
            counter_id_d = counter_id_q + 1;
        end else begin
            counter_id_d = counter_id_q;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            counter_id_q <= 0;
        end else begin
            counter_id_q <= counter_id_d;
        end
    end

    //////////////////////////////////////////////////////////////////////
    // General Element storage

    logic [2 ** ID_SIZE-1:0][$bits(DataType)-1:0] data_storage_d, data_storage_q;

    always_comb begin
        // Keep data as is as abase
        data_storage_d = data_storage_q;

        if ((failed_valid_q | valid_i) & ready_i) begin
            data_storage_d[counter_id_q] = data_o;
        end 
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            data_storage_q <= 0;
        end else begin
            data_storage_q <= data_storage_d;
        end
    end

    always_comb begin
        if (failed_valid_q & ready_i) begin
            data_o = data_storage_q[failed_id_q];
        end else if (valid_i & ready_i) begin
            data_o = data_i;
        end else begin
            data_o = '0;
        end
        id_o = counter_id_q;
    end 

    //////////////////////////////////////////////////////////////////////
    // Handshake assignment
    assign ready_o = ready_i & !failed_valid_q;
    assign valid_o = valid_i | failed_valid_q;

endmodule


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


