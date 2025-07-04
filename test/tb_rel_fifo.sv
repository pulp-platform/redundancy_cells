// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Testbench for generic FIFO
module tb_rel_fifo_inst #(
    // FIFO parameters
    parameter bit           FALL_THROUGH,
    parameter int unsigned  DEPTH,
    parameter int unsigned  DATA_WIDTH = 8,
    // TB parameters
    parameter int unsigned  N_CHECKS,
    parameter time          TA,
    parameter time          TT
) (
    input  logic    clk_i,
    input  logic    rst_ni,
    output logic    done_o
);

    import rand_verif_pkg::rand_wait;

    typedef logic [DATA_WIDTH-1:0] data_t;

    logic           clk,
                    flush,
                    full,
                    empty,
                    push,
                    pop,
                    try_push,
                    try_pop;

    logic [2:0] tmr_full,
                tmr_empty;

    data_t          wdata,
                    rdata;

    int unsigned    n_checks = 0;

    assign clk = clk_i;

    rel_fifo #(
        .FallThrough   ( FALL_THROUGH  ),
        .DataWidth     ( DATA_WIDTH    ),
        .Depth         ( DEPTH         ),
        .TmrStatus     ( 1'b1         ),
        .DataHasEcc    ( 1'b1         ),
        .StatusFF      ( 1'b0         ),
        .TmrBeforeReg  ( 1'b0         )
    ) dut (
        .clk_i,
        .rst_ni,
        .flush_i        ( {3{flush}}    ),
        .testmode_i     ( 1'b0          ),
        .full_o         ( tmr_full      ),
        .empty_o        ( tmr_empty     ),
        .usage_o        (               ),
        .data_i         ( wdata         ),
        .push_i         ( {3{push}}     ),
        .data_o         ( rdata         ),
        .pop_i          ( {3{pop}}      ),
        .fault_o        (               )
    );

    assign full  = tmr_full[0];
    assign empty = tmr_empty[0];

    // Simulation information and stopping.
    // TODO: Better stop after certain coverage is reached.
    initial begin
        done_o = 1'b0;
        $display("%m: Running test with FALL_THROUGH=%0d, DEPTH=%0d", FALL_THROUGH, DEPTH);
        wait (n_checks >= N_CHECKS);
        done_o = 1'b1;
        $display("%m: Checked %0d stimuli", n_checks);
    end

    class random_action_t;
        rand logic [1:0] action;
        constraint random_action {
            action dist {
                0 := 40,
                1 := 40,
                3 := 2,
                0 := 0
            };
        }
    endclass

    // Input driver: push, wdata, and flush
    assign push = try_push & ~full;
    initial begin
        automatic random_action_t rand_act = new();
        flush       <= 1'b0;
        wdata       <= 'x;
        try_push    <= 1'b0;
        wait (rst_ni);
        forever begin
            static logic rand_success;
            rand_wait(1, 8, clk);
            rand_success = rand_act.randomize(); assert(rand_success);
            case (rand_act.action)
                0: begin // new random data and try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b1;
                end
                1: begin // new random data but do not try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b0;
                end
                2: begin // flush
                    flush       <= #TA 1'b1;
                    rand_wait(1, 8, clk);
                    flush       <= #TA 1'b0;
                end
            endcase
        end
    end

    // Output driver: pop
    assign pop = try_pop & ~empty;
    initial begin
        try_pop <= 1'b0;
        wait (rst_ni);
        forever begin
            rand_wait(1, 8, clk);
            try_pop <= #TA $random();
        end
    end

    // Monitor & checker: model expected response and check against actual response
    initial begin
        data_t queue[$];
        wait (rst_ni);
        forever begin
            @(posedge clk_i);
            #(TT);
            if (flush) begin
                queue = {};
            end else begin
                if (push && !full) begin
                    queue.push_back(wdata);
                end
                if (pop && !empty) begin
                    automatic data_t data = queue.pop_front();
                    assert (rdata == data) else $error("Queue output %0x != %0x", rdata, data);
                    n_checks++;
                end
            end
        end
    end

    if (FALL_THROUGH) begin
        // In fall through mode, assert that the output data is equal to the input data when pushing
        // to an empty FIFO.
        assert property (@(posedge clk_i) ((empty & ~push) ##1 push) |-> rdata == wdata)
            else $error("Input did not fall through");
    end

endmodule

// Testbench for different FIFO configurations
module tb_rel_fifo #(
    // TB parameters
    parameter int unsigned  N_CHECKS        = 100000,
    parameter time          TCLK            = 10ns,
    parameter time          TA              = TCLK * 1/4,
    parameter time          TT              = TCLK * 3/4
);

    logic       clk,
                rst_n;

    logic [5:0] done;

    clk_rst_gen #(.ClkPeriod(TCLK), .RstClkCycles(10)) i_clk_rst_gen (
        .clk_o    (clk),
        .rst_no   (rst_n)
    );

    tb_rel_fifo_inst #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (8),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_8 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[0])
    );

    tb_rel_fifo_inst #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (8),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_8 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[1])
    );

    tb_rel_fifo_inst #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (1),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_1 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[2])
    );

    tb_rel_fifo_inst #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (1),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_1 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[3])
    );

    tb_rel_fifo_inst #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (9),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_9 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[4])
    );

    tb_rel_fifo_inst #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (9),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_9 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[5])
    );

    initial begin
        wait ((&done));
        $finish();
    end

endmodule
