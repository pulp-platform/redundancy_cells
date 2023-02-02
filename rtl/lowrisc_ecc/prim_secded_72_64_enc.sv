// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Encoder generated by
// util/design/secded_gen.py -m 8 -k 64 -s 1592631616 -c hsiao

module prim_secded_72_64_enc (
  input        [63:0] in,
  output logic [71:0] out
);

  always_comb begin : p_encode
    out[63:0] = in;
    out[64] = ^(in & 64'h5B000000001FFFFF);
    out[65] = ^(in & 64'h6B00000FFFE0003F);
    out[66] = ^(in & 64'h6D003FF003E007C1);
    out[67] = ^(in & 64'hAD0FC0F03C207842);
    out[68] = ^(in & 64'hB571C711C4438884);
    out[69] = ^(in & 64'hB6B65926488C9108);
    out[70] = ^(in & 64'hD6DAAA4A91152210);
    out[71] = ^(in & 64'hDAED348D221A4420);
  end

endmodule : prim_secded_72_64_enc