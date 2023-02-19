// Copyright 2023 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Rufer <lrufer@student.ethz.ch>

/// Fork a interrupt signal from a single source to multiple desinations.
/// The interrupt signal is directly forwarded the to all destinations. If an
/// error happenes in the receiving circuit, and the interrupt signal cannot be
/// handled, the external circuit can raise the 'repeat_i' signal. If the
/// interrupt signal was high in the cycle where 'repeat_i' was asserted, then
/// the interrupt signal will be repeated in the next clock cycle.

/// Interrupt signals are assumed to be active high and only asserted for a
/// single cycle.
/// This module can only handle a single outstanding interrupt at the time.

/// The internal state is TMR-protected, so SEUs cannot trigger an interrupt
/// by accident. All outputs have individual voters to protect agaist common-
/// mode SETs

module dmr_interrupt_fork #(
  parameter int  NUM_OUT     = 2
)(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,
  // repeat signals
  input  logic repeat_i,
  // interrupt signals
  input  logic               interrupt_i,
  output logic [NUM_OUT-1:0] interrupt_o
);

  // state signals (TMR protected)
  logic [2:0] outstanding_interrupt_d, outstanding_interrupt_q;

  // Other signals
  logic [NUM_OUT-1:0] outstanding_interrupt_voted;

  // Compute next state
  always_comb begin
    outstanding_interrupt_d = '0;
    if (repeat_i) begin
      outstanding_interrupt_d = {3{interrupt_i}} | outstanding_interrupt_q;
    end
  end

  // State
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      outstanding_interrupt_q <= '0;
    end else begin
      outstanding_interrupt_q <= outstanding_interrupt_d;
    end
  end

  for (genvar i = 0; i < NUM_OUT; i++) begin : gen_voters
    TMR_voter i_vote (
      .a_i        (outstanding_interrupt_q[0]),
      .b_i        (outstanding_interrupt_q[1]),
      .c_i        (outstanding_interrupt_q[2]),
      .majority_o (outstanding_interrupt_voted[i])
    );
  end

  // Generate output signals
  assign interrupt_o = {NUM_OUT{interrupt_i}} | outstanding_interrupt_voted;

  // --------------------
  //      Warnings
  // --------------------

  // pragma translate_off
  `ifndef VERILATOR
  // Source handshake assertions
  interrupt_overrun: assert property( @(posedge clk_i) disable iff (~rst_ni)
                (~(interrupt_i & &outstanding_interrupt_q))) else
                $warning("Interrupt Overrun.");
  `endif
  // pragma translate_on

endmodule
