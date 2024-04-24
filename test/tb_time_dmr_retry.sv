module tb_time_dmr_retry #(
    // DUT Parameters
    parameter int IDSize = 4,
    parameter int LockTimeout = 4,
    parameter bit InternalRedundancy = 0,

    // TB Parameters
    parameter int unsigned TESTS = 10000,
    parameter time CLK_PERIOD = 10ns,
    parameter time APPLICATION_DELAY = 2ns,
    parameter time AQUISITION_DELAY = 8ns
) ( /* no ports on TB */ );

    localparam unsigned RST_CLK_CYCLES = 10;

    // Parameters
    typedef logic [7:0] data_t;
    typedef logic [7:0] tag_t;

    typedef struct packed {
        data_t      data;
        tag_t       tag;
    } tagged_data_t;

    // Testbench signals
    tagged_data_t golden_queue [$];
    tagged_data_t data_golden, data_actual;
    logic error;
    int error_cnt;

    // Aux signals to show what faults are going on
    enum {NONE, DATA_ERROR, VALID_ERROR, READY_ERROR, ID_ERROR} fault_type, fault_current;

    // Signals for DUTS
    logic clk;
    logic rst_n;
    logic enable;

    // Downstream Connection
    tagged_data_t data_in,  data_detectable, data_redundant,  data_error,  data_redundant_faulty,  data_detected, data_out;
    logic valid_in, valid_detectable, valid_redundant, valid_error, valid_redundant_faulty, valid_detected, valid_out;
    logic ready_in, ready_detectable, ready_redundant, ready_error, ready_redundant_faulty, ready_detected, ready_out;
    logic [IDSize-1:0] id_detectable, id_redundant, id_error, id_redundant_faulty, id_detected, next_id;
    logic needs_retry_detected;

    // Feedback connection
    logic [IDSize-1:0] id_retry;
    logic valid_retry;
    logic ready_retry;

    // Clock Generation
    initial begin
        clk = '1;
        rst_n = '0;
        repeat (10) @(posedge clk);
        rst_n = 1;
    end

    always #((CLK_PERIOD/2)) clk = ~clk;

    // DUT Instances
    retry_start #(
        .DataType(tagged_data_t),
        .IDSize(IDSize)
    ) dut_retry_start (
        .clk_i(clk),
        .rst_ni(rst_n),

        // Upstream connection
        .data_i(data_in),
        .valid_i(valid_in),
        .ready_o(ready_in),

        // Downstream connection
        .data_o(data_detectable),
        .id_o(id_detectable),
        .valid_o(valid_detectable),
        .ready_i(ready_detectable),

        // Retry Connection
        .retry_id_i(id_retry),
        .retry_valid_i(valid_retry),
        .retry_ready_o(ready_retry)
    );


    // DUT Instances
    time_DMR_start #(
        .DataType(tagged_data_t),
        .IDSize(IDSize),
        .UseExternalId(1),
        .InternalRedundancy(InternalRedundancy)
    ) dut_DMR_start (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        .next_id_o(next_id),

        // Upstream connection
        .data_i(data_detectable),
        .id_i(id_detectable),
        .valid_i(valid_detectable),
        .ready_o(ready_detectable),

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

    // DUT Instances
    time_DMR_end #(
        .DataType(tagged_data_t),
        .LockTimeout(LockTimeout),
        .IDSize(IDSize),
        .InternalRedundancy(InternalRedundancy)
    ) dut_DMR_end (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        .next_id_i(next_id),

        // Upstream connection
        .data_i(data_redundant_faulty),
        .id_i(id_redundant_faulty),
        .valid_i(valid_redundant_faulty),
        .ready_o(ready_redundant),

        // Downstream connection
        .data_o(data_detected),
        .id_o(id_detected),
        .needs_retry_o(needs_retry_detected),
        .valid_o(valid_detected),
        .ready_i(ready_detected),
        .lock_o(/*Unused*/),

        .fault_detected_o(/*Unused*/)
    );

    // DUT Instances
    retry_end #(
        .DataType(tagged_data_t),
        .IDSize(IDSize)
    ) dut_retry_end (
        .clk_i(clk),                
        .rst_ni(rst_n),       

        // Upstream connection
        .data_i(data_detected),
        .id_i(id_detected),
        .needs_retry_i(needs_retry_detected),
        .valid_i(valid_detected),
        .ready_o(ready_detected),

        // Downstream connection
        .data_o(data_out),
        .valid_o(valid_out),
        .ready_i(ready_out),

        // Retry Connection
        .retry_id_o(id_retry),
        .retry_valid_o(valid_retry),
        .retry_ready_i(ready_retry)
    );

    // Data Application
    initial begin
        tag_t tag_new;
        tagged_data_t data_new;

        tag_new = 0;
        
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

            // Assign unique tag so we can
            tag_new += 1;
            data_new.data = $random;
            data_new.tag = tag_new;

            data_in = data_new;
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
                    ID_ERROR: id_error <= (1 << $urandom_range(0,IDSize-1));
                endcase
            end
            $display("Ending Test with fault type {%s}", fault_type.name());
        end
        $display("Checked %0d tests of each type, found %0d mismatches.", TESTS, error_cnt);
        $finish(0);
    end


    // Aquisition & Validation
    initial begin
        logic found;

        $timeformat(-9, 0, " ns", 20);

        // Initialize error metrics
        error = 0; // Signal so errors can easily be scrolled to in wave
        error_cnt = 0;
        found = 0;

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
                found = 0;

                repeat (golden_queue.size()) begin
                    data_golden = golden_queue.pop_front();
                    if (data_golden.tag == data_actual.tag) begin
                        // Check output
                        if (data_actual.data != data_golden.data) begin
                            $error("[T=%t] Mismatch: Golden: %h, Actual: %h", $time, data_golden, data_actual);
                            error = 1;
                            error_cnt += 1;
                        end else begin
                            error = 0;
                            found = 1;
                            break;
                        end
                    end else begin
                        golden_queue.push_back(data_golden);
                    end
                end
                if (found == 0) begin
                    $display("[T=%t] Tag %h Data %h Output but was not in golden queue ", $time, data_actual.tag, data_actual.data);
                    error = 1;
                    error_cnt += 1;
                end
            end else if (golden_queue.size() > 2 ** IDSize) begin
                $display("[T=%t] Data does not get output in a timely manner!", $time);
                error = 1;
                error_cnt += 1;     
            end else begin
                $display("[T=%t] Tag %h Data %h Output when nothing was in golden queue", $time, data_actual.tag, data_actual.data);
                error = 1;
                error_cnt += 1;
            end
        end
    end

endmodule
