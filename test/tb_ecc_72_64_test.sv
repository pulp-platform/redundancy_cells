// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// 
// Testbench for ECC 72_64

module tb_ecc_72_64_test;

  localparam int unsigned RunCycles    = 1000000;
  localparam time ClkPeriod            = 10ps;
  localparam time TApply               = 2ps;
  localparam time TTest                = 8ns;

  int flip_bit;
  int flip_bit2;

  logic clk, rst_n;

  logic [63:0] data_in, data_out;
  logic [71:0] data_protected_out, data_protected_in;
  logic [ 7:0] syndrome;
  logic [ 1:0] error;

  prim_secded_72_64_enc dut_encode (
    .in (data_in),
    .out(data_protected_out)
  );

  prim_secded_72_64_dec dut_decode (
    .in        (data_protected_in),
    .d_o       (data_out),
    .syndrome_o(syndrome),
    .err_o     (error)
  );

  always_comb begin
    data_protected_in = data_protected_out;
    for (int i = 0; i < 72; i++) begin
      if (i == flip_bit) begin
        data_protected_in[i] = ~data_protected_out[i];
      end
      if (i == flip_bit2) begin
        data_protected_in[i] = ~data_protected_out[i];
      end
    end  
  end

  initial begin
    flip_bit = 80;
    flip_bit2 = 80;

    // Test if data remains consistent for normal operation
    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      data_in = #TApply {$urandom(), $urandom()};
      #TTest;
      assert(data_out == data_in);
      assert(error == 2'b00);
      assert(syndrome == 7'b00);
    end

    // Test if data remains consistent for single bit error
    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      data_in = #TApply {$urandom(), $urandom()};
      flip_bit = $urandom_range(0,71);
      #TTest;
      assert(data_out == data_in);
      assert(error == 2'b01);
      assert(syndrome != 7'b00);
    end

    // Test if double errors are detected as such
    repeat(1) for (int i = 0; i < RunCycles; i++) begin
      data_in = #TApply {$urandom(), $urandom()};
      flip_bit = $urandom_range(0,71);
      flip_bit2 = $urandom_range(0,71);
      if (flip_bit2 == flip_bit) begin
        flip_bit2 = (flip_bit2+1)%72;
      end
      #TTest;
      assert(error == 2'b10);
    end
    
    $display("--------------------------------");
    $display("----------Reached End-----------");
    $stop();


  end

endmodule
