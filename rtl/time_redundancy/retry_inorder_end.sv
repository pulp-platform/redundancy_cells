// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 25.04.2024
// Description: retry is a pair of modules that can be used to run an operation
// passing through a (pipelined) combinatorial process.
//
// In order to propperly function:
// - id_o of retry_start needs to be passed paralelly along the combinatorial logic,
//   using the same handshake and arrive at id_i of retry_end
// - interface retry of retry_start needs to be directly connected to retry of retry_end
// - All elements in processing have a unique ID
//
// This module always keeps results in order by also retrying results that have been correct
// but at the wronge place or time.

`include "common_cells/registers.svh"

module retry_inorder_end # (
    parameter type DataType  = logic,
    parameter int IDSize = 1
) (
    input logic clk_i,
    input logic rst_ni,

    // Upstream connection
    input DataType data_i,
    input logic [IDSize-1:0] id_i,
    input logic needs_retry_i,
    input logic valid_i,
    output logic ready_o,

    // Downstream connection
    output DataType data_o,
    output logic valid_o,
    input logic ready_i,

    // Retry Connection
    retry_interface.ende retry
);

    // Signals do not change, only validity changes
    assign retry.id = id_i;
    assign data_o = data_i;

    logic [IDSize-1:0] failed_id_d, failed_id_q;
    logic retry_d, retry_q;

    always_comb begin: gen_next_state
        if (valid_i & retry_q) begin
            failed_id_d = failed_id_q;
            retry_d = ~(failed_id_q == id_i);
        end else if (valid_i & needs_retry_i) begin
            failed_id_d = retry.id_feedback;
            retry_d = 1;
        end else begin
            failed_id_d = failed_id_q;
            retry_d = retry_q;
        end
    end

    assign retry.lock = retry_d;

    `FF(retry_q, retry_d, '0);
    `FF(failed_id_q, failed_id_d, '0);

    always_comb begin: gen_output
        if (retry_d) begin
            retry.valid = valid_i;
            ready_o = retry.ready;
            valid_o = 0;
        end else begin
            valid_o = valid_i;
            ready_o = ready_i;
            retry.valid = 0;
        end
    end

endmodule


