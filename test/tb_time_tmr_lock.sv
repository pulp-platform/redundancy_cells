module tb_time_tmr_lock;
    // Clock Parameters

    timeunit 1ns;
    timeprecision 10ps;

    localparam time CLK_PERIOD = 10ns;
    localparam time APPLICATION_DELAY = 2ns;
    localparam time AQUISITION_DELAY = 8ns;
    localparam unsigned RST_CLK_CYCLES = 10;
    localparam unsigned TESTS = 10000;

    // Parameters
    typedef logic [7:0] data_t;
    parameter int NumOpgroups = 3;
    parameter int OpgroupWidth = 2;
    parameter int IDSize = 4;
    localparam int LockTimeout = 5;

    // Testebench signals
    data_t golden_queue [NumOpgroups-1:0][$];
    data_t data_golden, data_actual;
    logic [OpgroupWidth-1:0] operation_actual;
    logic error;
    int error_cnt;

    // Aux signals to show what faults are going on
    enum {NONE, DATA_ERROR, VALID_ERROR, READY_ERROR, ID_ERROR} fault_type, fault_current;

    // Signals for DUTS
    logic clk;
    logic rst_n;

    data_t in_data;
    logic [OpgroupWidth-1:0] in_operation;
    logic in_valid, in_ready;

    data_t data_error;
    logic valid_error, ready_error;
    logic [IDSize-1:0] id_error;

    data_t out_data;
    logic [OpgroupWidth-1:0] out_operation;
    logic out_valid, out_ready;

    // Clock Generation
    initial begin
        clk = '1;
        rst_n = '0;
        repeat (10) @(posedge clk);
        rst_n = 1;
    end

    always #((CLK_PERIOD/2)) clk = ~clk;

    // Instantiation of full fpnew datapath dut
    tb_time_tmr_lock_dut #(
        .DataType(data_t),       
        .NumOpgroups(NumOpgroups),
        .OpgroupWidth(OpgroupWidth),
        .IDSize(IDSize),
        .LockTimeout(LockTimeout),
        .OpgroupNumRegs({8'd4, 8'd3, 8'd3})
    ) dut (
        .clk_i(clk),                
        .rst_ni(rst_n),          

        // Ustream
        .operation_i(in_operation),
        .data_i(in_data),           
        .valid_i(in_valid),         
        .ready_o(in_ready),       

        .data_error_i     (data_error),
        .valid_error_i    (valid_error),
        .ready_error_i    (ready_error),
        .id_error_i       (id_error),

        // Downstream
        .operation_o(out_operation),
        .data_o(out_data),           
        .valid_o(out_valid),          
        .ready_i(out_ready)         
    );


    // Data Application
    initial begin
        data_t new_data;
        logic [OpgroupWidth-1:0] new_operation;

        // Initialize Handshake and Data
        in_data = 8'h00;
        in_operation = '0;
        in_valid = 1'b0;

        // Wait for reset to be lifted
        @(posedge rst_n);

        forever begin
            // Wait random time (with no valid data)
            repeat ($urandom_range(1, 10)) begin
                @(posedge clk);
                # APPLICATION_DELAY;
                in_valid = '0;
            end

            // Build next data element
            new_operation = $urandom_range(0, NumOpgroups-1);
            new_data = $random;

            // Apply Data
            in_data = new_data;
            in_operation = new_operation;
            in_valid = '1;

            // Save data for future
            golden_queue[new_operation].push_back(new_data);

            // Wait for handshake and as soon as it happens invalidate data
            # (AQUISITION_DELAY - APPLICATION_DELAY);
            while (!in_ready) begin
                @(posedge clk);
                # AQUISITION_DELAY;
            end;

        end
    end

    // Fault inject
    initial begin
        for (logic [2:0] ft = 0; ft < 5; ft++) begin
            fault_type[2:0] = ft;
            $display("Starting Test with fault type {%s}", fault_type.name());

            repeat (TESTS) begin

                // Send correct data for some cycles to space errors
                repeat ($urandom_range(45, 55)) begin
                    @(posedge clk);
                    # (APPLICATION_DELAY);
                    fault_current = NONE;          
                    data_error = '0; 
                    valid_error = '0;
                    ready_error = '0;
                    id_error = '0;
                end

                // Send wrong data
                @(posedge clk);
                # (APPLICATION_DELAY);
                fault_current <= fault_type; 
                data_error <= '0; 
                valid_error <= '0;
                ready_error <= '0;     
                case (fault_type)
                    DATA_ERROR: data_error <= $random;
                    VALID_ERROR: valid_error <= 1;
                    READY_ERROR: ready_error <= 1;
                    ID_ERROR: id_error <= $random;
                endcase
            end
            $display("Ending Test with fault type {%s}", fault_type.name());
        end
        $display("Checked %0d tests of each type, found %0d mismatches.", TESTS, error_cnt);
        $finish(error_cnt);
    end


    // Aquisition & Validation
    initial begin
        $timeformat(-9, 0, " ns", 20);


        // Initialize Handshake
        out_ready = '0;

        // Wait for reset to be lifted
        @(posedge rst_n);

        forever begin
            // Wait random time (while not ready)
            repeat ($urandom_range(1, 10)) begin
                @(posedge clk);
                # APPLICATION_DELAY;
                out_ready = '0;
            end

            // Set ready
            out_ready = '1;

            // Wait for handshake
            # (AQUISITION_DELAY - APPLICATION_DELAY);
            while (!out_valid) begin
                @(posedge clk);
                # AQUISITION_DELAY;
            end;

            // Once it happened check if output was good and reset ready again
            data_actual = out_data;
            operation_actual = out_operation;
            if (golden_queue[out_operation].size() > 0) begin
                data_golden = golden_queue[out_operation].pop_front();
                if (data_actual != data_golden) begin
                    $display("[T=%t] Operation %h -> Data %h Mismatch, should be %h", $time, operation_actual, data_actual, data_golden);
                    error = 1;
                    error_cnt += 1;
                end else begin
                    error = 0;
                end
            end else begin
                $display("[T=%t] Operation %h -> Data %h Output when nothing was in golden queue", $time, operation_actual, data_actual);
                error = 1;
                error_cnt += 1;
            end
        end
    end

endmodule : tb_time_tmr_lock