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

/// Fork some handshaked data from a single source to multiple desinations.
/// All destinations must recieve the same output signals, but may provide
/// different input signals (only due to fault-induced errors, not by design).
/// This module makes sure all handshakes with the source are correctly handled,
/// and every transaction is completed exactly once without errors with every
/// destination.
///
/// This module has three different error signals. Their effects are described
/// below:
/// - 'error_before_i': Error in the logic before the module (with respect to
///   the 'ready_i' signals of the destinations).
///   Some other logic block detected an error, which makes the 'ready_i'
///   signals (from the destination) that are supplied here unreliable.
///   The module will ignore the 'ready_i' signals from the destinations and
///   maintain the 'ready_o' signal (to the source) the from the previous cycle.
/// - 'error_o': The Module detected a mismatch in the 'ready_i' signals.
///   This has the same effect as an asserted 'error_before_i' signal.
/// - 'error_after_i': Some logic that depends on the destination output signals
///   of this module detected an error/mismatch, and the current cycle must be
///   repeated. When this signal is asserted and there was a completed handshake
///   on the destination side, this module will repeat the completed transaction
///   in the next clock cycle.
///   The 'error_after_i' signal does not affect the handshake signals, it only
///   effects the modules' internal state. This is done to prevent combinatorial
///   loops and reduce the critical timing path.
///
/// If the 'enable_i' signal is high, the module behaves as described above.
/// If it is low, the checking features of the module are disabled:
/// - Incomming error signals are ignored
/// - The outgoing 'error_o' signal will always be 0
/// - Handshakes will only be completed with destination 0. While all
///   desitinations still receive the same data via 'data_o', only the valid
///   signal of destination 0 is used, all other valid signals are set to 0.
///   Equally, only the ready signal of destination 0 is used to complete the
///   handshake, all other ready signals are ignored.
/// It is in the responsibility of the user to make sure a change in the
/// 'enable_i' signal will not violate any handshake rules.

module dmr_handshake_fork #(
  parameter type T           = logic,
  parameter int  NUM_OUT     = 2
)(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,
  // enable signal
  input  logic enable_i,
  // error signals
  input  logic error_before_i,
  input  logic error_after_i,
  output logic error_o,
  // data source
  input  logic valid_i,
  output logic ready_o,
  input  T     data_i,
  // data destination
  output logic [NUM_OUT-1:0] valid_o,
  input  logic [NUM_OUT-1:0] ready_i,
  output T     [NUM_OUT-1:0] data_o
);

  // state signals
  logic ready_d, ready_q;
  logic data_latched_d, data_latched_q;
  T data_d, data_q;

  // intermediate signals
  logic source_hs_complete, dest_hs_complete;

  // check if handshakes completed
  assign source_hs_complete = ready_o & valid_i;
  assign dest_hs_complete = &(ready_i & valid_o) & ~error_after_i & ~error_before_i;

  // --------------------
  //   Output signals
  // --------------------

  always_comb begin
    // check if module is enabled
    if(enable_i) begin
      // Destination
      for (int unsigned i = 0; i < NUM_OUT; i++) begin
        valid_o[i] = valid_i | data_latched_q;
        data_o[i] = (data_latched_q) ? data_q : data_i;
      end

      // Source
      ready_o = (ready_q | (&ready_i & ~error_before_i)) & ~data_latched_q;

      // Error
      error_o = ~((&ready_i) | (ready_i == '0));

    end else begin
      // Destination
      valid_o = '0;
      valid_o[0] = valid_i;
      data_o = {NUM_OUT{data_i}};

      // Source
      ready_o = ready_i[0];

      // Error
      error_o = 1'b0;
    end
  end

  // --------------------
  //  Compute next state
  // --------------------

  // Ready signal (dest -> source)
  always_comb begin
    // default state
    ready_d = ready_q;
    // set ready signals if all destinations are ready, and no error
    if (&ready_i & !error_before_i) begin
      ready_d = 1'b1;
    end
    // clear ready signal if handshake is completed with source
    if (source_hs_complete) begin
      ready_d = 1'b0;
    end
    // Clear state if fork is disabled
    if (!enable_i) begin
      ready_d = 1'b0;
    end
  end

  // Data (source -> dest)
  always_comb begin
    // default state
    data_latched_d = data_latched_q;
    data_d = data_q;
    // if handshake with source is complete, but destination is not, then latch data
    if (source_hs_complete & ~dest_hs_complete) begin
      data_latched_d = 1'b1;
      data_d = data_i;
    end
    // if handshake with destination is complete, clear data
    if (dest_hs_complete) begin
      data_latched_d = 1'b0;
    end
    // Clear state if fork is disabled
    if (!enable_i) begin
      data_latched_d = 1'b0;
    end
  end

  // --------------------
  //        State
  // --------------------
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      ready_q <= '0;
      data_latched_q <= '0;
      data_q <= '0;
    end else begin
      ready_q <= ready_d;
      data_latched_q <= data_latched_d;
      data_q <= data_d;
    end
  end

  // --------------------
  //      Assertions
  // --------------------

  // pragma translate_off
  `ifndef VERILATOR
  // Source handshake assertions
  source_valid: assert property( @(posedge clk_i) disable iff (~rst_ni)
                (valid_i & ~ready_o |=> valid_i)) else
                $fatal(1, "Deasserted valid before complete source handshake.");
  source_data:  assert property( @(posedge clk_i) disable iff (~rst_ni)
                (valid_i & ~ready_o |=> $stable(data_i))) else
                $fatal(1, "Unstable data before complete source handshake.");
  dest_ready:   assert property( @(posedge clk_i) disable iff (~rst_ni)
                ((enable_i & error_after_i & ~error_before_i & ~error_o |=> $stable(ready_i)))) else
                $warning("Ready signals were modified during a repetition cycle.");
  `endif
  // pragma translate_on

endmodule
