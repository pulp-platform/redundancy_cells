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

// This file contains a handshaked data source and a handshaked data sink,
// that are designed to be used togehter in testbenches for DMR circuits.
// These modules are similar to the 'rand_stream' modules provided in the
// 'common verification' repo, with two main differences important for testing
// DMR circutis:
// 1. The data this source provides is deterministic and implemented as a
//    counter starting at 0. This allows to quickly find dropped and repeated
//    transactions, as well as out-of-order arrival. This is automatically
//    checked at the sink.
// 2. The modules have an input to allow (and ignore) handshakes. This can be
//    helpful in circuits (like DMR protected circuits) where a data
//    transaction cannot be completed even tough the handshake was completed
//    (due to errors in the state or somewhere else in the circuit).

module handshake_source #(
    parameter int unsigned DATA_BITS = 0,
    parameter bit          WARN_NEXT_ITEM_OVERRUN = 0
  ) (
    // clock and reset
    input  logic                 clk_i,
    input  logic                 rst_ni,
    // control signals
    input  logic                 next_item_i,
    input  logic                 allow_handshake_i,
    // data
    output logic                 valid_o,
    input  logic                 ready_i,
    output logic [DATA_BITS-1:0] data_o
  );

    // Signals
    logic [DATA_BITS-1:0] data_d, data_q;
    logic                 valid_d, valid_q;
    logic                 handshake_complete;

    // assignments
    assign data_o = data_q;
    assign valid_o = valid_q;
    assign handshake_complete = allow_handshake_i & valid_o & ready_i;

    always_comb begin
      // default
      data_d = data_q;
      valid_d = valid_q;

      // check if handshake complete
      if(handshake_complete) begin
        valid_d = 1'b0;
        data_d = data_q + 1;
      end

      // Next item in the next cycle
      if(next_item_i) begin
        valid_d = 1'b1;
      end
    end

    // State
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        data_q <= '0;
        valid_q <= '0;
      end else begin
        data_q <= data_d;
        valid_q <= valid_d;
      end
    end

    `ifndef VERILATOR
    // pragma translate_off
    // Warnings
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      ( data_q != 0 |-> data_d != 0)) else
      $warning("[Handshake Source] data_o overflow!");
    if(WARN_NEXT_ITEM_OVERRUN) begin
      assert property (@(posedge clk_i) disable iff (~rst_ni)
        ( next_item_i |-> ((valid_o & ready_i) | ~valid_o))) else
        $warning("[Handshake Source] next_item overrun!");
    end

    // Assertions (external checks)
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      (( ready_i & ~valid_o ) |=> ready_i)) else
      $error("[Handshake Source] ready revoked before handshake completed.");

    // Assertions (internal checks)
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      (~ready_i &  valid_o ) |=> valid_o) else
      $error("[Handshake Source] valid revoked before handshake completed.");
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      (~ready_i &  valid_o ) |=> $stable(data_o)) else
      $error("[Handshake Source] data changed before handshake completed.");

    // pragma translate_on
    `endif

  endmodule

  module handshake_sink #(
    parameter int unsigned DATA_BITS = 0
  ) (
    // clock and reset
    input  logic                 clk_i,
    input  logic                 rst_ni,
    // control signals
    input  logic                 raise_ready_i,
    input  logic                 allow_sink_i,
    // data
    input  logic                 valid_i,
    output logic                 ready_o,
    input  logic [DATA_BITS-1:0] data_i,
    // testbench
    output logic [DATA_BITS-1:0] next_expected_o,
    output logic [DATA_BITS-1:0] num_received_o
  );

    // Signals
    logic                 ready_d, ready_q;
    logic                 handshake_complete;

    // assignments
    assign ready_o = ready_q;
    assign handshake_complete = allow_sink_i & valid_i & ready_o;

    always_comb begin
      // default
      ready_d = ready_q;

      // check if handshake complete
      if(handshake_complete) begin
        ready_d = 1'b0;
      end

      // Next item in the next cycle
      if(raise_ready_i) begin
        ready_d = 1'b1;
      end
    end

    // State
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        ready_q <= '0;
      end else begin
        ready_q <= ready_d;
      end
    end

    // testbench only
    time                  last_consumed;
    logic [DATA_BITS-1:0] data_expected;
    logic [DATA_BITS-1:0] num_received;

    initial begin
      last_consumed = 0;
      data_expected = 0;
      num_received = 0;
      forever begin
        @(posedge clk_i);
        if(handshake_complete) begin
          num_received++;
          if(data_i > data_expected) begin
            $error("[Handshake Sink] received %0d, expected %0d. %0d Data Items were skipped. Last item consumed at %0t",
              data_i, data_expected, $signed(data_i)-$signed(data_expected), last_consumed);
          end else if (data_i < data_expected) begin
            $error("[Handshake Sink] received %0d, expected %0d. Data Item was repeated or out of order. Last item consumed at %0t",
              data_i, data_expected, last_consumed);
          end
          last_consumed = $time;
          data_expected = data_i + 1;
        end
      end
    end

    assign next_expected_o = data_expected;
    assign num_received_o = num_received;

    // Assertions (internal checks)
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      ( ready_o & ~valid_i ) |=> ready_o) else
      $error("[Handshake Sink] ready revoked before handshake completed.");

    // Assertions (external checks)
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      ( ~ready_o & valid_i ) |=> valid_i) else
      $error("[Handshake Sink] valid revoked before handshake completed.");
    assert property (@(posedge clk_i) disable iff (~rst_ni)
      ( ~ready_o & valid_i ) |=> $stable(data_i)) else
      $error("[Handshake Sink] data changed before handshake completed.");

  endmodule
