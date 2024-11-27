`include "common_cells/registers.svh"

module tb_retry_inorder;

    // Clock Parameters
    localparam time CLK_PERIOD = 10ns;
    localparam time APPLICATION_DELAY = 2ns;
    localparam time AQUISITION_DELAY = 8ns;
    localparam unsigned RST_CLK_CYCLES = 10;
    localparam unsigned TESTS = 10000;

    // Parameters
    typedef logic [7:0] data_t;
    parameter IDSize = 4;
    localparam int unsigned NUM_REGS = 4;

    // Testbench signals
    data_t golden_queue [$];
    data_t data_golden, data_actual;
    logic error;
    int error_cnt;

    // Signals for DUTS
    logic clk;
    logic rst_n;

    data_t data_in, data_out;
    logic valid_in, valid_out;
    logic ready_in, ready_out;
    logic needs_retry_middle;

    retry_interface #(.IDSize(IDSize)) retry_connection ();

    data_t [0:NUM_REGS] data_middle;
    logic [0:NUM_REGS] valid_middle;
    logic [0:NUM_REGS] ready_middle;
    logic [0:NUM_REGS][IDSize-1:0] id_middle;

    // Clock Generation
    initial begin
        clk = '1;
        rst_n = '0;
        repeat (10) @(posedge clk);
        rst_n = 1;
    end

    always #((CLK_PERIOD/2)) clk = ~clk;

    // DUT Instances
    retry_inorder_start #(
        .DataType(data_t),
        .IDSize(IDSize)
    ) dut_start (
        .clk_i(clk),
        .rst_ni(rst_n),

        // Upstream connection
        .data_i(data_in),
        .valid_i(valid_in),
        .ready_o(ready_in),

        // Downstream connection
        .data_o(data_middle[0]),
        .id_o(id_middle[0]),
        .valid_o(valid_middle[0]),
        .ready_i(ready_middle[0]),

        // Retry Connection
        .retry(retry_connection)
    );

    // Generate the register stages
    for (genvar i = 0; i < NUM_REGS; i++) begin : gen_pipeline
        // Internal register enable for this stage
        logic reg_ena;

        // Determine the ready signal of the current stage - advance the pipeline:
        // 1. if the next stage is ready for our data
        // 2. if the next stage only holds a bubble (not valid) -> we can pop it
        assign ready_middle[i] = ready_middle[i+1] | ~valid_middle[i+1];

        // Valid: enabled by ready signal, synchronous clear with the flush signal
        `FFLARNC(valid_middle[i+1], valid_middle[i], ready_middle[i], 1'b0, 1'b0, clk, rst_n)
        // Enable register if pipleine ready and a valid data item is present
        assign reg_ena = (ready_middle[i] & valid_middle[i]);  // | reg_ena_i[i];
        // Generate the pipeline registers within the stages, use enable-registers
        `FFLARN(data_middle[i+1],      data_middle[i],      reg_ena, '0, clk, rst_n)
        `FFLARN(  id_middle[i+1],      id_middle[i],        reg_ena, '0, clk, rst_n)
    end

    retry_inorder_end #(
        .DataType(data_t),
        .IDSize(IDSize)
    ) dut_end (
        .clk_i(clk),
        .rst_ni(rst_n),

        // Upstream connection
        .data_i(data_middle[NUM_REGS]),
        .id_i(id_middle[NUM_REGS]),
        .needs_retry_i(needs_retry_middle),
        .valid_i(valid_middle[NUM_REGS]),
        .ready_o(ready_middle[NUM_REGS]),

        // Downstream connection
        .data_o(data_out),
        .valid_o(valid_out),
        .ready_i(ready_out),

        // Retry Connection
        .retry(retry_connection)
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

    // Drive Fault signal
    initial begin
        repeat (TESTS) begin

            // Send correct data for some cycles to space errors
            repeat ($urandom_range(15, 20)) begin
                @(posedge clk);
                # (APPLICATION_DELAY);
                needs_retry_middle = '0;
            end

            @(posedge clk);
            # (APPLICATION_DELAY);
            needs_retry_middle = '1;

            // Wait for handshake
            # (AQUISITION_DELAY - APPLICATION_DELAY);
            while (!(ready_middle[NUM_REGS] & valid_middle[NUM_REGS])) begin
                @(posedge clk);
                # AQUISITION_DELAY;
            end
        end

        $display("Checked %0d tests of each type, found %0d mismatches.", TESTS, error_cnt);
        $finish(0);
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
