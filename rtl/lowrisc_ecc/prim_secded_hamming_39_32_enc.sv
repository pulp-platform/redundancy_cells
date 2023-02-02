// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Encoder generated by
// util/design/secded_gen.py -m 7 -k 32 -s 1592631616 -c hamming

module prim_secded_hamming_39_32_enc (
  input        [31:0] in,
  output logic [38:0] out
);

  always_comb begin : p_encode
    out[31:0] = in;
    out[32] = ^(in & 32'h56AAAD5B);
    out[33] = ^(in & 32'h9B33366D);
    out[34] = ^(in & 32'hE3C3C78E);
    out[35] = ^(in & 32'h03FC07F0);
    out[36] = ^(in & 32'h03FFF800);
    out[37] = ^(in & 32'hFC000000);
    out[38] = ^(in & 32'h2DA65CB7);
  end

endmodule : prim_secded_hamming_39_32_enc