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

/// Join handshaked data from multiple sources to a single desination.
/// All sources must recieve the same ready signal from the destination, but
/// may provide different input signals (only due to fault-induced errors,
/// not by design).
/// This module makes sure all handshakes with the destination are correctly
/// handled. Transaction with the source are only done when all sources agree
/// on the same data and valid signals, and every transaction is completed
/// exactly once.
///
/// This module has three different error signals. Their effects are described
/// below:
/// - 'error_before_i': Error before the module.
///   Some other logic block detected an error, which makes the source signals
///   (data_i and valid_i) unreliable.
///   The module will ignore the 'valid_i' signals from the sources and maintain
///   the 'valid_o' and 'data_o' signals (to the destination) from the
///   previous cycle (except if the handshake on the destination side was
///   completed, in wich case the 'valid_o' signal is pulled low afterwards).
/// - 'error_o': The Module detected a mismatch in the 'valid_i' signals, or
///   a mismatch in the 'data_i' signals while all 'valid_i' signals were
///   active.
///   This has the same effect as an asserted 'error_before_i' signal.
/// - 'error_after_i': Some logic that depends on the destination output signals
///   of this module ('ready_o') detected an error/mismatch, and the current
///   cycle must be repeated to correctly handle the ready_o signals.
///   This module makes sure that if a transaction was completed in the same
///   cycle as the 'error_after_i' signal is active, no transaction will be
///   issued during the repetition cycle, so that the same transaction is not
///   issued twice. Note that completing a transaction during a cycle with an
///   'after error' and trying to complete another transaction during the
///   repetition cycle will result in the second transaction not being
///   completed!
///   The 'error_after_i' signal does not affect the handshake signals, it only
///   effects the modules' internal state. This is done to prevent combinatorial
///   loops and reduce the critical timing path.

module dmr_handshake_join #(
  parameter type T      = logic,
  parameter int  NUM_IN = 2
)(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,
  // error signals
  input  logic error_before_i,
  input  logic error_after_i,
  output logic error_o,
  // data source
  input  logic [NUM_IN-1:0] valid_i,
  output logic [NUM_IN-1:0] ready_o,
  input  T     [NUM_IN-1:0] data_i,
  // data destination
  output logic valid_o,
  input  logic ready_i,
  output T     data_o
);

  // state signals
  logic valid_d, valid_q;
  logic repeat_ready_d, repeat_ready_q;
  logic error_after_d, error_after_q;
  T data_d, data_q;

  // intermediate signals
  logic source_hs_complete, dest_hs_complete;

  // check if handshakes complete
  assign dest_hs_complete = ready_i & valid_o;
  assign source_hs_complete = &(ready_o & valid_i) & ~error_after_i & ~error_o & ~error_before_i;

  // --------------------
  //   Output signals
  // --------------------

  // Destination
  always_comb begin
    valid_o = valid_i;
    data_o = data_i[0];
    if (error_after_q) begin
      valid_o = valid_i | valid_q;
    end
    if (error_before_i | error_o) begin
      valid_o = valid_q;
      data_o = data_q;
    end
    if (repeat_ready_q) begin
      valid_o = 1'b0;
    end
  end

  // Source
  for(genvar i = 0; i < NUM_IN; i++) begin
    assign ready_o[i] = ready_i | repeat_ready_q;
  end

  // Error
  always_comb begin
    error_o = error_before_i;
    // check if all valid signals agree
    if(~((&valid_i) | (valid_i == '0))) begin
      error_o = 1'b1;
    end
    // check if valid signals were revoked
    if(valid_q & ~(&valid_i)) begin
      error_o = 1'b1;
    end
    // if valid, check if all data inputs match
    if(&valid_i) begin
      for(int unsigned i = 1; i < NUM_IN; i++) begin
        if(data_i[i] != data_i[i-1]) begin
          error_o = 1'b1;
        end
      end
    end
  end

  // --------------------
  //  Compute next state
  // --------------------

  // Valid and Data signals (sources -> dest)
  always_comb begin
    // default state
    valid_d = valid_o;
    data_d = data_o;
    // set valid signal if all sources are valid, and no error before or detected
    if (&valid_i & !error_before_i & !error_o & !error_after_q) begin
      valid_d = 1'b1;
      data_d = data_i[0];
    end
    // clear valid signal if handshake is completed with destination
    if (dest_hs_complete | repeat_ready_q) begin
      valid_d = 1'b0;
    end
  end

  // Ready (dest -> sources)
  always_comb begin
    // default state
    repeat_ready_d = repeat_ready_q;
    // if handshake with source is complete, but destination is not, then latch data
    if (dest_hs_complete & ~source_hs_complete) begin
      repeat_ready_d = 1'b1;
    end
    // if handshake with destination is complete, clear data
    if (source_hs_complete) begin
      repeat_ready_d = 1'b0;
    end
  end

  // Internal
  always_comb begin
    error_after_d = error_after_i & !(error_o | error_before_i);
  end

  // --------------------
  //        State
  // --------------------
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= '0;
      repeat_ready_q <= '0;
      error_after_q <= '0;
      data_q <= '0;
    end else begin
      valid_q <= valid_d;
      repeat_ready_q <= repeat_ready_d;
      error_after_q <= error_after_d;
      data_q <= data_d;
    end
  end

  // --------------------
  //      Assertions
  // --------------------

  // pragma translate_off
  `ifndef VERILATOR
  // Destination handshake assertions
  dest_ready:   assert property( @(posedge clk_i) disable iff (~rst_ni)
                (ready_i & ~valid_o |=> ready_i)) else
                $fatal(1, "Deasserted ready before complete destination handshake.");
  `endif
  // pragma translate_on

endmodule
