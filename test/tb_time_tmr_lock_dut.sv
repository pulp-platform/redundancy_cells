`include "../../common_cells/include/common_cells/registers.svh"


module tb_time_tmr_lock_dut # (
    // What kind of data signal to pass through the chain
    parameter type DataType  = logic,
    parameter int LockTimeout = 5,

    // How many parallel instances to generate and how many registers they should each have
    parameter int NumOpgroups = 3,
    parameter int OpgroupWidth = 2,
    parameter int IDSize = 4,
    parameter [NumOpgroups-1:0][7:0] OpgroupNumRegs = {8'd10, 8'd10, 8'd10}
) (
    input logic clk_i,
    input logic rst_ni,

    // Upstream connection
    input logic [OpgroupWidth-1:0] operation_i,
    input DataType data_i,
    input logic valid_i,
    output logic ready_o,

    // Error Injection
    input DataType data_error_i,
    input logic [IDSize-1:0] id_error_i,
    input logic valid_error_i,
    input logic ready_error_i,

    // Downstream connection
    output logic [OpgroupWidth-1:0] operation_o,
    output DataType data_o,
    output logic valid_o,
    input logic ready_i
);
    
    // Typedef for stacked signal in TMR
    typedef struct packed {
        DataType                       data;
        logic [$bits(operation_i)-1:0] operation;
    } tmr_stacked_t;

    // Typedef for stacked signal in TMR
    typedef struct packed {
        logic [IDSize-1:0] id;
        DataType            data;
    } rr_stacked_t;

    // Input connection
    tmr_stacked_t in_tmr_stack;
    assign in_tmr_stack.data = data_i;
    assign in_tmr_stack.operation = operation_i;

    // Signals for after TMR
    tmr_stacked_t in_tmr_stack_redundant;
    logic in_valid_redundant, in_ready_redundant;
    logic [IDSize-1:0] in_id_redundant;
    
    time_TMR_start #(
        .DataType(tmr_stacked_t),
        .IDSize (IDSize)
    ) i_time_TMR_start (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .enable_i(1'b1),

        // Upstream connection
        .data_i(in_tmr_stack),
        .valid_i(valid_i),
        .ready_o(ready_o),

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

        DataType               [0:NUM_REGS]                 pipe_data;
        logic                  [0:NUM_REGS]                 pipe_valid;
        logic                  [0:NUM_REGS]                 pipe_ready;
        logic     [0:NUM_REGS][IDSize-1:0]                 pipe_id;

        // Upstream Connection
        // Error Injection
        assign pipe_valid[0]  = in_valid_redundant ^ valid_error_i && (opgrp == in_tmr_stack_redundant.operation);
        assign pipe_data[0]   = in_tmr_stack_redundant.data ^ data_error_i;
        assign pipe_id[0]      = in_id_redundant ^ id_error_i;
        assign in_opgrp_ready[opgrp] = pipe_ready[0] ^ ready_error_i;

        // Generate the register stages
        for (genvar i = 0; i < NUM_REGS; i++) begin : gen_pipeline
            // Internal register enable for this stage
            logic reg_ena;

            // Determine the ready signal of the current stage - advance the pipeline:
            // 1. if the next stage is ready for our data
            // 2. if the next stage only holds a bubble (not valid) -> we can pop it
            assign pipe_ready[i] = pipe_ready[i+1] | ~pipe_valid[i+1];

            // Valid: enabled by ready signal, synchronous clear with the flush signal
            `FFLARNC(pipe_valid[i+1], pipe_valid[i], pipe_ready[i], 1'b0, 1'b0, clk_i, rst_ni)
            // Enable register if pipleine ready and a valid data item is present
            assign reg_ena = (pipe_ready[i] & pipe_valid[i]);  // | reg_ena_i[i];
            // Generate the pipeline registers within the stages, use enable-registers
            `FFL(pipe_data[i+1],      pipe_data[i],      reg_ena, DataType'('0))
            `FFL(  pipe_id[i+1],      pipe_id[i],        reg_ena, IDSize'('0))
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
        .clk_i(clk_i),
        .rst_ni(rst_ni),
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
    logic [IDSize-1:0] out_tmr_id;

    assign out_tmr_id = out_rr_stack.id;
    assign out_tmr_stack.data = out_rr_stack.data;


    time_TMR_end #(
        .DataType(tmr_stacked_t),
        .LockTimeout(LockTimeout),
        .IDSize (IDSize)
    ) i_time_TMR_end (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .enable_i(1'b1),

        // Upstream connection
        .data_i(out_tmr_stack),
        .id_i   (out_tmr_id),
        .valid_i(out_tmr_valid),
        .ready_o(out_tmr_ready),

        // Downstream connection
        .data_o(out_stacked),
        .valid_o(valid_o),
        .ready_i(ready_i),
        .lock_o(lock),

        // Flags
        .fault_detected_o(/* Unused */)
    );

    assign data_o = out_stacked.data;
    assign operation_o = out_stacked.operation;

endmodule: tb_time_tmr_lock_dut