// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Chaoqun Liang <chaoqun.liang@unibo.it>

module rel_delta_counter #(
  parameter int unsigned WIDTH           = 4,
  parameter bit          STICKY_OVERFLOW = 1'b0
)(
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  logic                  clear_i,    // synchronous clear
  input  logic                  en_i,       // enable the counter
  input  logic                  load_i,     // load a new value
  input  logic                  down_i,     // downcount, default is up
  input  logic [WIDTH-1:0]      delta_i,
  input  logic [WIDTH-1:0]      d_i,
  output logic [2:0][WIDTH-1:0] q_o,        
  output logic [2:0]            overflow_o, 
  output logic                  fault_o     
);
  // stores data and carry
  logic [2:0][WIDTH:0] counter_sync;
  logic [2:0][1:0][WIDTH:0] alt_counter_sync;
  
  logic [2:0]            overflow_sync;
  logic [2:0][1:0]       alt_overflow_sync;

  logic [2:0]            tmr_fault;
  assign fault_o = |tmr_fault;
  
  for (genvar i = 0; i < 3; i++) begin : gen_alt_sync
    for (genvar j = 0; j < 2; j++) begin : gen_alt
      assign alt_counter_sync[i][j]  = counter_sync[(i+j+1) % 3];
      assign alt_overflow_sync[i][j] = overflow_sync[(i+j+1) % 3];
    end
  end
  
  for (genvar i = 0; i < 3; i++) begin : gen_tmr_parts
    rel_delta_counter_tmr_part #(
      .WIDTH           ( WIDTH           ),
      .STICKY_OVERFLOW ( STICKY_OVERFLOW )
    ) i_tmr_part (
      .clk_i               ( clk_i                  ),
      .rst_ni              ( rst_ni                 ),
      .clear_i             ( clear_i                ),
      .en_i                ( en_i                   ),
      .load_i              ( load_i                 ),
      .down_i              ( down_i                 ),
      .delta_i             ( delta_i                ),
      .d_i                 ( d_i                    ),
      .alt_counter_sync_i  ( alt_counter_sync[i]    ),
      .counter_sync_o      ( counter_sync[i]        ),
      .alt_overflow_sync_i ( alt_overflow_sync[i]   ),
      .overflow_sync_o     ( overflow_sync[i]       ),
      .q_o                 ( q_o[i]                 ),
      .overflow_o          ( overflow_o[i]          ),
      .fault_o             ( tmr_fault[i]           )
    );
  end

endmodule

  (* no_ungroup *)
  (* no_boundary_optimization *)
  module rel_delta_counter_tmr_part #(
    parameter int unsigned WIDTH           = 4,
    parameter bit          STICKY_OVERFLOW = 1'b0
  )(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  clear_i,
    input  logic                  en_i,
    input  logic                  load_i,
    input  logic                  down_i,
    input  logic [WIDTH-1:0]      delta_i,
    input  logic [WIDTH-1:0]      d_i,
    input  logic [1:0][WIDTH:0]   alt_counter_sync_i,
    output logic      [WIDTH:0]   counter_sync_o,     
    input  logic [1:0]            alt_overflow_sync_i,
    output logic                  overflow_sync_o,    
    // outputs
    output logic [WIDTH-1:0]      q_o,
    output logic                  overflow_o,
    output logic                  fault_o
  );
  
  logic [WIDTH:0] counter_q;   // own register
  logic [WIDTH:0] counter_voted; // locally voted result
  logic [WIDTH:0] counter_d;
  logic           counter_fault;

  assign counter_sync_o = counter_q;
  
  bitwise_TMR_voter_fail #(
    .DataWidth ( WIDTH+1 )
  ) i_counter_vote (
    .a_i              ( counter_q              ), // own raw register
    .b_i              ( alt_counter_sync_i[0]  ), // replica j raw
    .c_i              ( alt_counter_sync_i[1]  ), // replica k raw
    .majority_o       ( counter_voted          ),
    .fault_detected_o ( counter_fault          )
  );

  always_comb begin
    counter_d = counter_voted;
    if (clear_i)
      counter_d = '0;
    else if (load_i)
      counter_d = {1'b0, d_i};
    else if (en_i)
      counter_d = down_i ? (counter_voted - {1'b0, delta_i})
                         : (counter_voted + {1'b0, delta_i});
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) counter_q <= '0;
      else         counter_q <= counter_d;
  end

  assign q_o = counter_q[WIDTH-1:0];

  if (STICKY_OVERFLOW) begin : gen_sticky_overflow

    logic overflow_q;
    logic overflow_voted;
    logic overflow_d;
    logic overflow_fault;
    
    assign overflow_sync_o = overflow_q;

    TMR_voter_fail #(
      .VoterType ( 1 )
    ) i_overflow_vote (
      .a_i              ( overflow_q              ),
      .b_i              ( alt_overflow_sync_i[0]  ),
      .c_i              ( alt_overflow_sync_i[1]  ),
      .majority_o       ( overflow_voted          ),
      .fault_detected_o ( overflow_fault          )
    );

    always_comb begin
      overflow_d = overflow_voted;
      if (clear_i || load_i)
        overflow_d = 1'b0;
      else if (!overflow_voted && en_i)
		    overflow_d = down_i ? (delta_i > counter_voted[WIDTH-1:0])
                            : (counter_voted[WIDTH-1:0] > ({WIDTH{1'b1}} - delta_i));
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) overflow_q <= 1'b0;
        else         overflow_q <= overflow_d;
    end

    assign overflow_o = overflow_q;
    assign fault_o    = counter_fault | overflow_fault;

  end else begin : gen_transient_overflow

    assign overflow_sync_o = counter_q[WIDTH];
    assign overflow_o      = counter_q[WIDTH];
    assign fault_o         = counter_fault;

  end

endmodule
