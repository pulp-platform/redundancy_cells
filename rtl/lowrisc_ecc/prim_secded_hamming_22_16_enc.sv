// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Encoder generated by
// util/design/secded_gen.py -m 6 -k 16 -s 1592631616 -c hamming

module prim_secded_hamming_22_16_enc (
  input        [15:0] in,
  output logic [21:0] out
);

  always_comb begin : p_encode
    out[15:0] = in;
    out[16] = ^(in & 16'hAD5B);
    out[17] = ^(in & 16'h366D);
    out[18] = ^(in & 16'hC78E);
    out[19] = ^(in & 16'h07F0);
    out[20] = ^(in & 16'hF800);
    out[21] = ^(in & 16'h5CB7);
  end

endmodule : prim_secded_hamming_22_16_enc
