module tb_time_dmr #(
    // DUT Parameters
    parameter IDSize = 4,
    parameter int LockTimeout = 4 * 12,
    parameter bit InternalRedundancy = 0,

    // TB Parameters
    parameter int unsigned TESTS = 10000,
    parameter time CLK_PERIOD = 10ns,
    parameter time APPLICATION_DELAY = 2ns,
    parameter time AQUISITION_DELAY = 8ns

) ( /* no ports on TB */ );

   `include "tb_time.svh"

    //////////////////////////////////////////////////////////////////////////////////7
    // DUT (s)
    //////////////////////////////////////////////////////////////////////////////////7

    typedef logic [7:0] data_t;

    data_t data_in, data_redundant,  data_fault,  data_redundant_faulty,  data_out;
    logic valid_redundant, valid_fault, valid_redundant_faulty;
    logic ready_redundant, ready_fault, ready_redundant_faulty;
    logic [IDSize-1:0] id_redundant, id_fault, id_redundant_faulty, id_next;

    // DUT Instances
    time_DMR_start #(
        .DataType(data_t),
        .IDSize(IDSize),
        .UseExternalId(0),
        .InternalRedundancy(InternalRedundancy)
    ) dut_start (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        .next_id_o(id_next),

        // Upstream connection
        .data_i(data_in),
        .id_i('0),
        .valid_i(valid_in),
        .ready_o(ready_in),

        // Downstream connection
        .data_o(data_redundant),
        .id_o(id_redundant),
        .valid_o(valid_redundant),
        .ready_i(ready_redundant_faulty)
    );

    time_DMR_end #(
        .DataType(data_t),
        .LockTimeout(LockTimeout),
        .IDSize(IDSize),
        .InternalRedundancy(InternalRedundancy)
    ) dut_end (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        .next_id_i(id_next),


        // Upstream connection
        .data_i(data_redundant_faulty),
        .id_i(id_redundant_faulty),
        .valid_i(valid_redundant_faulty),
        .ready_o(ready_redundant),
        .lock_o(/*Unused*/),

        // Downstream connection
        .data_o(data_out),
        .id_o(/*Unused*/),
        .needs_retry_o(needs_retry_out),
        .valid_o(valid_out),
        .ready_i(ready_out),

        .fault_detected_o(/*Unused*/)
    );

    //////////////////////////////////////////////////////////////////////////////////7
    // Data Input
    //////////////////////////////////////////////////////////////////////////////////7
    data_t golden_queue [$];

    initial begin
        forever begin
            input_handshake_begin();
            data_in = $random;
            golden_queue.push_back(data_in);
            input_handshake_end();
        end
    end


    //////////////////////////////////////////////////////////////////////////////////7
    // Data Output
    //////////////////////////////////////////////////////////////////////////////////7
    data_t data_golden, data_actual;
    logic needs_retry_actual;
    logic error; // Helper signal so one can quickly scroll to errors in questa
    longint unsigned error_cnt = 0;
    int fault_budget = 0;

    // Progress reporting
    task reset_metrics();
        reset();
        error_cnt = 0;
        in_hs_count = 0;
        out_hs_count = 0;
        golden_queue.delete();
    endtask

    initial begin
        $timeformat(-9, 0, " ns", 20);
        forever begin
            output_handshake_start();
            data_actual = data_out;
            needs_retry_actual = needs_retry_out;
            if (golden_queue.size() > 0) begin
                data_golden = golden_queue.pop_front();

                if (needs_retry_actual) begin
                    fault_budget -= 1;
                    if (fault_budget < 0) begin
                        $error("[T=%t] More faults detected than injected!", $time);
                        error = 1;
                        error_cnt += 1;
                    end
                end else begin
                    if (data_actual != data_golden) begin
                        $error("[T=%t] Mismatch: Golden: %h, Actual: %h", $time, data_golden, data_actual);
                        error = 1;
                        error_cnt += 1;
                    end else begin
                        fault_budget = 1;
                        error = 0;
                    end
                end

            end else begin
                $display("[T=%t] Data %h Output when nothing was in golden queue", $time, data_actual);
                error = 1;
                error_cnt += 1;
            end
            output_handshake_end();
        end
    end

    //////////////////////////////////////////////////////////////////////////////////7
    // Fault Injection
    //////////////////////////////////////////////////////////////////////////////////7

    longint unsigned min_fault_delay = 12 * 4;
    longint unsigned max_fault_delay = 12 * 4 + 20;

    // Signals to show what faults are going on
    enum {NONE, DATA_FAULT, VALID_FAULT, READY_FAULT, ID_FAULT} fault_type, fault_current;

    assign data_redundant_faulty =  data_redundant ^  data_fault;
    assign valid_redundant_faulty = (valid_redundant & stall) ^ valid_fault;
    assign ready_redundant_faulty = (ready_redundant & stall) ^ ready_fault;
    assign id_redundant_faulty = id_redundant ^ id_fault;

    initial data_fault  = '0;
    initial valid_fault = '0;
    initial ready_fault = '0;
    initial id_fault    = '0;

    task inject_fault();
        // Send correct data for some cycles to space errors
        repeat ($urandom_range(min_fault_delay, max_fault_delay)) begin
            @(posedge clk);
            fault_current = NONE;
            data_fault = '0;
            valid_fault = '0;
            ready_fault = '0;
            id_fault = '0;
        end

        // Send wrong data
        fault_current = fault_type;
        case (fault_type)
            DATA_FAULT: data_fault <= $random;
            VALID_FAULT: valid_fault <= 1;
            READY_FAULT: ready_fault <= 1;
            ID_FAULT: id_fault <= (1 << $urandom_range(0,IDSize-1));
        endcase

        fault_budget += 1;

        // Send correct data again
        @(posedge clk);
        fault_current = NONE;
        data_fault = '0;
        valid_fault = '0;
        ready_fault = '0;
        id_fault = '0;
    endtask

    //////////////////////////////////////////////////////////////////////////////////7
    // Main Loop
    //////////////////////////////////////////////////////////////////////////////////7
    longint unsigned total_error_cnt = 0;

    initial begin
        reset_metrics();

        // Check normal operation
        fault_type = NONE;
        enable = 0;
        repeat (10 * TESTS) @(posedge clk);
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc disabled and no faults, got %d errors.", error_cnt);
        reset_metrics();

        enable = 1;
        repeat (TESTS) @(posedge clk);
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled and no faults, got %d errors.", error_cnt);
        reset_metrics();

        // Check fault tolerance
        fault_type = DATA_FAULT;
        enable = 1;
        repeat (TESTS) inject_fault();
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled and data faults, got %d errors.", error_cnt);
        reset_metrics();

        fault_type = VALID_FAULT;
        enable = 1;
        repeat (TESTS) inject_fault();
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled and valid fault, got %d errors.", error_cnt);
        reset_metrics();

        fault_type = READY_FAULT;
        enable = 1;
        repeat (TESTS) inject_fault();
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled and ready faults, got %d errors.", error_cnt);
        reset_metrics();

        fault_type = ID_FAULT;
        enable = 1;
        repeat (TESTS) inject_fault();
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled and ID faults, got %d errors.", error_cnt);
        reset_metrics();

        // Measure throughput
        fault_type = NONE;
        enable = 0;
        in_hs_max_starvation = 0;
        out_hs_max_starvation = 0;
        internal_hs_max_starvation = 0;
        repeat (TESTS) @(posedge clk);
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc disabled got a max throughtput of %d/%d and %d errors.", out_hs_count, TESTS, error_cnt);
        if (TESTS - out_hs_count > TESTS / 20) begin
            $error("Stall detected with ecc disabled!");
        end
        reset_metrics();

        enable = 1;
        repeat (TESTS) @(posedge clk);
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled got a max throughtput of %d/%d and %d errors.", out_hs_count, TESTS /2, error_cnt);
        if (TESTS /2 - out_hs_count > TESTS / 20) begin
            $error("Stall detected with ecc enabled!");
        end
        reset_metrics();
        $display("Checked %0d tests of each type, found %0d mismatches.", TESTS, total_error_cnt);
        $finish(error_cnt);
    end

endmodule
