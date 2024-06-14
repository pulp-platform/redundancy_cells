`include "common_cells/registers.svh"

module tb_time_tmr_lock #(
    // DUT Parameters
    parameter int LockTimeout = 5,
    parameter int NumOpgroups = 3,
    parameter int OpgroupWidth = $clog2(NumOpgroups),
    parameter int IDSize = 5,
    parameter [NumOpgroups-1:0][7:0] OpgroupNumRegs = {8'd4, 8'd3, 8'd3},
    parameter bit EarlyValidEnable = 0,
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

    typedef logic              [7:0] data_t;
    typedef logic [OpgroupWidth-1:0] operation_t;
    typedef logic       [IDSize-1:0] id_t;

    // Typedef for stacked signal in TMR
    typedef struct packed {
        data_t      data;
        operation_t operation;
    } tmr_stacked_t;

    // Typedef for stacked signal in TMR
    typedef struct packed {
        id_t        id;
        data_t      data;
    } rr_stacked_t;

    // Input & Output
    data_t data_in, data_out;
    operation_t operation_in, operation_out;

    // Fault Connections for Injection
    data_t  data_fault;
    logic valid_fault;
    logic  ready_fault;
    id_t id_fault;

    tmr_stacked_t in_tmr_stack;
    assign in_tmr_stack.data = data_in;
    assign in_tmr_stack.operation = operation_in;

    // Signals for after TMR
    tmr_stacked_t in_tmr_stack_redundant;
    logic in_valid_redundant, in_ready_redundant;
    id_t in_id_redundant;

    time_TMR_start #(
        .DataType(tmr_stacked_t),
        .IDSize (IDSize),
        .InternalRedundancy(InternalRedundancy)
    ) i_time_TMR_start (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        // Upstream connection
        .data_i(in_tmr_stack),
        .valid_i(valid_in),
        .ready_o(ready_in),

        // Downstream connection
        .data_o(in_tmr_stack_redundant),
        .id_o   (in_id_redundant),
        .valid_o(in_valid_redundant),
        .ready_i(in_ready_redundant)
    );

    // Handshake signal array for opgroup block
    logic [NumOpgroups-1:0] in_opgrp_ready, out_opgrp_valid, out_opgrp_ready;
    rr_stacked_t [NumOpgroups-1:0] out_opgrp_rr_stack;
    rr_stacked_t out_rr_stack;

    // Pass ready up based on the current operation_i
    assign in_ready_redundant = in_valid_redundant & in_opgrp_ready[in_tmr_stack_redundant.operation];

    for (genvar opgrp = 0; opgrp < int'(NumOpgroups); opgrp++) begin : gen_operation_groups
        localparam NUM_REGS = OpgroupNumRegs[opgrp];

        // Input pipeline signals, index i holds signal after i register stages
        data_t [0:NUM_REGS] pipe_data;
        logic  [0:NUM_REGS] pipe_valid;
        logic  [0:NUM_REGS] pipe_ready;
        id_t   [0:NUM_REGS] pipe_id;

        // Upstream Connection
        // Error Injection
        assign pipe_valid[0]  = (in_valid_redundant ^ valid_fault) && (opgrp == in_tmr_stack_redundant.operation);
        assign pipe_data[0]   = in_tmr_stack_redundant.data ^ data_fault;
        assign pipe_id[0]      = in_id_redundant ^ id_fault;
        assign in_opgrp_ready[opgrp] = pipe_ready[0] ^ ready_fault;

        // Generate the register stages
        for (genvar i = 0; i < NUM_REGS; i++) begin : gen_pipeline
            // Internal register enable for this stage
            logic reg_ena;

            // Determine the ready signal of the current stage - advance the pipeline:
            // 1. if the next stage is ready for our data
            // 2. if the next stage only holds a bubble (not valid) -> we can pop it
            assign pipe_ready[i] = pipe_ready[i+1] | ~pipe_valid[i+1];

            // Valid: enabled by ready signal, synchronous clear with the flush signal
            `FFLARNC(pipe_valid[i+1], pipe_valid[i], pipe_ready[i], 1'b0, 1'b0, clk, rst_n)
            // Enable register if pipleine ready and a valid data item is present
            assign reg_ena = (pipe_ready[i] & pipe_valid[i]);  // | reg_ena_i[i];
            // Generate the pipeline registers within the stages, use enable-registers
            `FFLARN(pipe_data[i+1],      pipe_data[i],      reg_ena, data_t'('0), clk, rst_n)
            `FFLARN(  pipe_id[i+1],      pipe_id[i],        reg_ena, id_t'('0), clk, rst_n)
        end

        // Downstream connection
        assign out_opgrp_valid[opgrp] = pipe_valid[NUM_REGS];
        assign out_opgrp_rr_stack[opgrp].data  = pipe_data[NUM_REGS];
        assign out_opgrp_rr_stack[opgrp].id    = pipe_id[NUM_REGS];
        assign pipe_ready[NUM_REGS]   = out_opgrp_ready[opgrp];
    end

    // Signals for after RR
    logic out_tmr_valid, out_tmr_ready;
    tmr_stacked_t out_tmr_stack;

    // Backpropagating lock signal
    logic lock;

    // Round-Robin arbiter to decide which result to use
    rr_arb_tree_lock #(
        .NumIn     ( NumOpgroups ),
        .DataType  ( rr_stacked_t  ),
        .AxiVldRdy ( 1'b1         )
    ) i_arbiter (
        .clk_i(clk),
        .rst_ni(rst_n),
        .flush_i('0),
        .rr_i   ('0),
        .lock_rr_i (lock),

        // Upstream connection
        .req_i(out_opgrp_valid),
        .gnt_o(out_opgrp_ready),
        .data_i(out_opgrp_rr_stack),

        // Downstream connection
        .gnt_i(out_tmr_ready),
        .req_o(out_tmr_valid),
        .data_o(out_rr_stack),
        .idx_o(out_tmr_stack.operation)
    );


    // Signals for after TMR
    tmr_stacked_t out_stacked;
    id_t out_tmr_id;

    assign out_tmr_id = out_rr_stack.id;
    assign out_tmr_stack.data = out_rr_stack.data;

    time_TMR_end #(
        .DataType(tmr_stacked_t),
        .LockTimeout(LockTimeout),
        .IDSize (IDSize),
        .EarlyValidEnable(EarlyValidEnable),
        .InternalRedundancy(InternalRedundancy)
    ) i_time_TMR_end (
        .clk_i(clk),
        .rst_ni(rst_n),
        .enable_i(enable),

        // Upstream connection
        .data_i(out_tmr_stack),
        .id_i   (out_tmr_id),
        .valid_i(out_tmr_valid),
        .ready_o(out_tmr_ready),

        // Downstream connection
        .data_o(out_stacked),
        .valid_o(valid_out),
        .ready_i(ready_out),
        .lock_o(lock),

        // Flags
        .fault_detected_o(/* Unused */)
    );

    assign data_out = out_stacked.data;
    assign operation_out = out_stacked.operation;

    //////////////////////////////////////////////////////////////////////////////////7
    // Data Input
    //////////////////////////////////////////////////////////////////////////////////7
    data_t golden_queue [NumOpgroups-1:0][$];

    initial begin
        forever begin
            input_handshake_begin();
            operation_in = $urandom_range(0, NumOpgroups-1);;
            data_in = $random;
            golden_queue[operation_in].push_back(data_in);
            input_handshake_end();
        end
    end

    //////////////////////////////////////////////////////////////////////////////////7
    // Data Output
    //////////////////////////////////////////////////////////////////////////////////7
    data_t data_golden, data_actual;
    logic [OpgroupWidth-1:0] operation_actual;
    logic error; // Helper signal so one can quickly scroll to errors in questa
    longint unsigned error_cnt = 0;

    // Progress reporting
    task reset_metrics();
        reset();
        error_cnt = 0;
        in_hs_count = 0;
        out_hs_count = 0;
        for (int i = 0; i < NumOpgroups; i++) begin
            golden_queue[i].delete();
        end
    endtask

    initial begin
        $timeformat(-9, 0, " ns", 20);
        forever begin
            output_handshake_start();
            // Once it happened check if output was good and reset ready again
            data_actual = data_out;
            operation_actual = operation_out;
            if (golden_queue[operation_actual].size() > 0) begin
                data_golden = golden_queue[operation_actual].pop_front();
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
            output_handshake_end();
        end
    end

    //////////////////////////////////////////////////////////////////////////////////7
    // Fault Injection
    //////////////////////////////////////////////////////////////////////////////////7

    longint unsigned min_fault_delay = 45;
    longint unsigned max_fault_delay = 55;

    // Signals to show what faults are going on
    enum {NONE, DATA_FAULT, VALID_FAULT, READY_FAULT, ID_FAULT} fault_type, fault_current;

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
            DATA_FAULT: data_fault = $random;
            VALID_FAULT: valid_fault = 1;
            READY_FAULT: ready_fault = 1;
            ID_FAULT: id_fault = $random;
        endcase

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
        repeat (TESTS) @(posedge clk);
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc disabled got a max throughtput of %d/%d and %d errors.", out_hs_count, TESTS, error_cnt);
        reset_metrics();

        enable = 1;
        repeat (TESTS) @(posedge clk);
        total_error_cnt += error_cnt;
        $display("Ending Test with ecc enabled got a max throughtput of %d/%d and %d errors.", out_hs_count, TESTS, error_cnt);
        reset_metrics();
        $display("Checked %0d tests of each type, found %0d mismatches.", TESTS, total_error_cnt);
        $finish(error_cnt);
    end


endmodule
