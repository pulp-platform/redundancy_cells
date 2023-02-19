// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Decoder generated by
// util/design/secded_gen.py -m 3 -k 1 -s 1592631616 -c hsiao

module prim_secded_4_1_dec (
  input        [3:0] in,
  output logic [0:0] d_o,
  output logic [2:0] syndrome_o,
  output logic [1:0] err_o
);

  logic single_error;

  // Syndrome calculation
  assign syndrome_o[0] = ^(in & 4'h3);
  assign syndrome_o[1] = ^(in & 4'h5);
  assign syndrome_o[2] = ^(in & 4'h9);

  // Corrected output calculation
  assign d_o[0] = (syndrome_o == 3'h7) ^ in[0];

  // err_o calc. bit0: single error, bit1: double error
  assign single_error = ^syndrome_o;
  assign err_o[0] = single_error;
  assign err_o[1] = ~single_error & (|syndrome_o);

endmodule : prim_secded_4_1_dec
