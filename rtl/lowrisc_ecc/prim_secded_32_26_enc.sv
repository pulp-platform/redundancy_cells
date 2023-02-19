// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Encoder generated by
// util/design/secded_gen.py -m 6 -k 26 -s 1592631616 -c hsiao

module prim_secded_32_26_enc (
  input        [25:0] in,
  output logic [31:0] out
);

  always_comb begin : p_encode
    out[25:0] = in;
    out[26] = ^(in & 26'h1F003FF);
    out[27] = ^(in & 26'h2F0FC0F);
    out[28] = ^(in & 26'h3771C71);
    out[29] = ^(in & 26'h3BB6592);
    out[30] = ^(in & 26'h3DDAAA4);
    out[31] = ^(in & 26'h3EED348);
  end

endmodule : prim_secded_32_26_enc
