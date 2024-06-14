module tb_time_tmr;

    // Clock Parameters
    localparam time CLK_PERIOD = 10ns;
    localparam time APPLICATION_DELAY = 2ns;
    localparam time AQUISITION_DELAY = 8ns;
    localparam unsigned RST_CLK_CYCLES = 10;
    localparam unsigned TESTS = 10000;

    // Parameters
    typedef logic [7:0] data_t;
    parameter IDSize = 4;
    localparam int LockTimeout = 4;

    // Testbench signals
    data_t golden_queue [$];
    data_t data_golden, data_actual;
    logic error;
    int error_cnt;

    // Aux signals to show what faults are going on
    enum {NONE, DATA_ERROR, VALID_ERROR, READY_ERROR, ID_ERROR} fault_type, fault_current;

    // Signals for DUTS
    logic clk;
    logic rst_n;
    logic enable;

    data_t data_in,  data_redundant,  data_error,  data_redundant_faulty,  data_out;
    logic valid_in, valid_redundant, valid_error, valid_redundant_faulty, valid_out;
    logic ready_in, ready_redundant, ready_error, ready_redundant_faulty, ready_out;
    logic [IDSize-1:0] id_redundant, id_error, id_redundant_faulty;

    // Clock Generation
    initial begin
        clk = '1;
        rst_n = '0;
        repeat (10) @(posedge clk);
        rst_n = 1;
    end

    always #((CLK_PERIOD/2)) clk = ~clk;

    // DUT Instances
    time_TMR_start #(
        .DataType(data_t),
        .IDSize(IDSize)
    ) dut_start (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        // Upstream connection
        .data_i(data_in),
        .valid_i(valid_in),
        .ready_o(ready_in),

        // Downstream connection
        .data_o(data_redundant),
        .id_o(id_redundant),
        .valid_o(valid_redundant),
        .ready_i(ready_redundant_faulty)
    );

    // Error XORs
    assign  data_redundant_faulty =  data_redundant ^  data_error;
    assign valid_redundant_faulty = valid_redundant ^ valid_error;
    assign ready_redundant_faulty = ready_redundant ^ ready_error;
    assign id_redundant_faulty = id_redundant ^ id_error;

    time_TMR_end #(
        .DataType(data_t),
        .LockTimeout(LockTimeout),
        .IDSize(IDSize)
    ) dut_end (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        // Upstream connection
        .data_i(data_redundant_faulty),
        .id_i(id_redundant_faulty),
        .valid_i(valid_redundant_faulty),
        .ready_o(ready_redundant),

        // Downstream connection
        .data_o(data_out),
        .valid_o(valid_out),
        .ready_i(ready_out),
        .lock_o(/*Unused*/),

        // Flags
        .fault_detected_o(/* Unused */)
    );

    // Data Application
    initial begin
        // Initialize Handshake and Data
        data_in = 8'h00;
        valid_in = 1'b0;

        // Wait for reset to be lifted
        @(posedge rst_n);

        forever begin
            // Wait random time (with no valid data)
            repeat ($urandom_range(1, 5)) begin
                @(posedge clk);
                # APPLICATION_DELAY;
                valid_in <= '0;
            end

            valid_in <= '1;
            data_in = $random;
            golden_queue.push_back(data_in);

            // Wait for handshake and as soon as it happens invalidate data
            # (AQUISITION_DELAY - APPLICATION_DELAY);
            while (!ready_in) begin
                @(posedge clk);
                # AQUISITION_DELAY;
            end;

        end
    end

    // Enable / Disable ECC
    initial begin
        enable = 1'b0;
        $display("Disabled Redundancy");
        repeat (TESTS * 5) begin
            @(posedge clk);
        end
        $display("Enabled Redundancy");
        enable = 1'b1;
    end

    // Fault inject
    initial begin
        for (logic [2:0] ft = 0; ft < 5; ft++) begin
            fault_type[2:0] = ft;
            $display("Starting Test with fault type {%s}", fault_type.name());

            repeat (TESTS) begin

                // Send correct data for some cycles to space errors
                repeat ($urandom_range(15, 20)) begin
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
                id_error <= '0;
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

        // Initialize error metrics
        error = 0; // Signal so errors can easily be scrolled to in wave
        error_cnt = 0;

        // Initialize Handshake
        ready_out = '0;

        // Wait for reset to be lifted
        @(posedge rst_n);

        forever begin
            // Wait random time (while not ready)
            repeat ($urandom_range(1, 5)) begin
                @(posedge clk);
                # APPLICATION_DELAY;
                ready_out <= '0;
            end

            // Set ready
            ready_out <= '1;

            // Wait for handshake
            # (AQUISITION_DELAY - APPLICATION_DELAY);
            while (!valid_out) begin
                @(posedge clk);
                # AQUISITION_DELAY;
            end;

            // Once it happened check if output was good and reset ready again
            data_actual = data_out;
            if (golden_queue.size() > 0) begin
                data_golden = golden_queue.pop_front();
                // Check output
                if (data_actual != data_golden) begin
                    $error("[T=%t] Mismatch: Golden: %h, Actual: %h", $time, data_golden, data_actual);
                    error = 1;
                    error_cnt += 1;
                end else begin
                    error = 0;
                end
            end else begin
                $display("[T=%t] Data %h Output when nothing was in golden queue", $time, data_actual);
                error = 1;
                error_cnt += 1;
            end
        end
    end

endmodule
