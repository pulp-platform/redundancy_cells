// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 25.04.2024
// Module that can correctly enable / disable time_TMR or time_DMR modules
// when they do not hold valid data. It does so by stalling the handshake
// upstream of the redundancy modules until they are empty,
// then enables / disables them.
//
// Caveat: In case a fault occurs while this module is trying to switch to a non-redundant mode
// the module might currently stall since not all data in the combinatorial process can propperly
// be consumed and the condition for switching can not be reached.
// Switching back to the redundant mode will unstall the setup.

`include "voters.svh"
`include "common_cells/registers.svh"

module redundancy_controller # (
    // Determines if the internal state machines should
    // be parallely redundant, meaning errors inside this module
    // can also not cause errors in the output
    // The external output is never protected!
    parameter bit InternalRedundancy = 0,
    // Do not modify
    localparam int REP = InternalRedundancy ? 3 : 1
) (
    input logic clk_i,
    input logic rst_ni,

    // Connection to outside
    input logic enable_i,
    output logic busy_o,

    // Connection to redundancy modules
    input logic busy_i,
    output logic enable_o,

    // Upstream Handshake
    input logic valid_i,
    output logic ready_o,

    // Downstream Handshake
    output logic valid_o,
    input logic ready_i
);

    // Redundant versions of output signals
    logic valid_ov[REP];
    logic ready_ov[REP];
    logic busy_ov[REP];
    logic enable_ov[REP];

    logic enable_v[REP], enable_d[REP], enable_q[REP];

    for (genvar r = 0; r < REP; r++) begin: gen_next_state
      always_comb begin
        if (busy_i) begin
          enable_v[r] = enable_q[r];
        end else begin
          enable_v[r] = enable_i;
        end
      end
    end

    // State Voting Logic
    if (InternalRedundancy) begin : gen_state_voters
        `VOTE3to3(enable_v, enable_d);
    end else begin
        assign enable_d = enable_v;
    end

    // Generate default case
    logic enable_base[REP];
    for (genvar r = 0; r < REP; r++) begin: gen_default_state
        assign enable_base[r] = '0;
    end

    `FFARN(enable_q, enable_d, enable_base, clk_i, rst_ni);

    // Output combinatorial logic
    for (genvar r = 0; r < REP; r++) begin: gen_output
        always_comb begin
            enable_ov[r] = enable_q[r];

            if (enable_q[r] == enable_i) begin
                valid_ov[r] = valid_i;
                ready_ov[r] = ready_i;
                busy_ov[r] = busy_i;
            end else begin
                valid_ov[r] = 1'b0;
                ready_ov[r] = 1'b0;
                busy_ov[r] = 1'b1;
            end
        end
    end

    // Output voting logic
    if (InternalRedundancy) begin: gen_output_voters
        `VOTE3to1(enable_ov, enable_o);
        `VOTE3to1(valid_ov, valid_o);
        `VOTE3to1(ready_ov, ready_o);
        `VOTE3to1(busy_ov, busy_o);
    end else begin: gen_output_passthrough
        assign enable_o = enable_ov[0];
        assign valid_o = valid_ov[0];
        assign ready_o = ready_ov[0];
        assign busy_o = busy_ov[0];
    end

endmodule
