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
  logic [2:0][WIDTH:0] counter_q;

  // Majority vote over the three replicas, self-correcting
  logic [WIDTH:0] counter_voted;
  logic           counter_fault;

  bitwise_TMR_voter_fail #(
    .DataWidth ( WIDTH+1 )
  ) i_counter_vote (
    .a_i              ( counter_q[0]  ),
    .b_i              ( counter_q[1]  ),
    .c_i              ( counter_q[2]  ),
    .majority_o       ( counter_voted ),
    .fault_detected_o ( counter_fault )
  );

  logic [WIDTH:0] counter_d;
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

  always_ff @(posedge clk_i or negedge rst_ni)
    for (int i = 0; i < 3; i++)
      if (!rst_ni) counter_q[i] <= '0;
      else         counter_q[i] <= counter_d;
  
  // q_o data bits only
  for (genvar j = 0; j < 3; j++)
    assign q_o[j] = counter_q[j][WIDTH-1:0];

  if (STICKY_OVERFLOW) begin : gen_sticky_overflow
    logic [2:0] overflow_q;
    logic       overflow_voted, overflow_d;
    logic       overflow_fault;

    bitwise_TMR_voter_fail #(
      .DataWidth ( 1 )
    ) i_overflow_vote (
      .a_i              ( overflow_q[0]  ),
      .b_i              ( overflow_q[1]  ),
      .c_i              ( overflow_q[2]  ),
      .majority_o       ( overflow_voted ),
      .fault_detected_o ( overflow_fault )
    );

    always_comb begin
      overflow_d = overflow_voted;
      if (clear_i || load_i)
        overflow_d = 1'b0;
      else if (!overflow_voted && en_i)
		overflow_d = down_i ? (delta_i > counter_voted[WIDTH-1:0])
                            : (counter_voted[WIDTH-1:0] > ({WIDTH{1'b1}} - delta_i));
    end

    always_ff @(posedge clk_i or negedge rst_ni)
      for (int i = 0; i < 3; i++)
        if (!rst_ni) overflow_q[i] <= 1'b0;
        else         overflow_q[i] <= overflow_d;

    for (genvar n = 0; n < 3; n++)
      assign overflow_o[n] = overflow_q[n];

    assign fault_o    = counter_fault | overflow_fault;

  end else begin : gen_transient_overflow

    for (genvar n = 0; n < 3; n++) begin : gen_overflow_replicas
		assign overflow_o[n] = counter_q[n][WIDTH];
	end
    assign fault_o    = counter_fault;
  end

endmodule
