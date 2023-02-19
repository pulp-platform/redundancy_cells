// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Corrector generated by
// util/design/secded_gen.py -m 8 -k 64 -s 1592631616 -c hsiao

module prim_secded_72_64_cor (
  input        [71:0] d_i,
  output logic [71:0] d_o,
  output logic [7:0] syndrome_o,
  output logic [1:0] err_o
);

  logic single_error;

  // Syndrome calculation
  assign syndrome_o[0] = ^(d_i & 72'h01F8000000001FFFFF);
  assign syndrome_o[1] = ^(d_i & 72'h029D00000FFFE0003F);
  assign syndrome_o[2] = ^(d_i & 72'h048F003FF003E007C1);
  assign syndrome_o[3] = ^(d_i & 72'h08F10FC0F03C207842);
  assign syndrome_o[4] = ^(d_i & 72'h106E71C711C4438884);
  assign syndrome_o[5] = ^(d_i & 72'h203EB65926488C9108);
  assign syndrome_o[6] = ^(d_i & 72'h40D3DAAA4A91152210);
  assign syndrome_o[7] = ^(d_i & 72'h8067ED348D221A4420);

  // Corrected output calculation
  assign d_o[0] = (syndrome_o == 8'h7) ^ d_i[0];
  assign d_o[1] = (syndrome_o == 8'hb) ^ d_i[1];
  assign d_o[2] = (syndrome_o == 8'h13) ^ d_i[2];
  assign d_o[3] = (syndrome_o == 8'h23) ^ d_i[3];
  assign d_o[4] = (syndrome_o == 8'h43) ^ d_i[4];
  assign d_o[5] = (syndrome_o == 8'h83) ^ d_i[5];
  assign d_o[6] = (syndrome_o == 8'hd) ^ d_i[6];
  assign d_o[7] = (syndrome_o == 8'h15) ^ d_i[7];
  assign d_o[8] = (syndrome_o == 8'h25) ^ d_i[8];
  assign d_o[9] = (syndrome_o == 8'h45) ^ d_i[9];
  assign d_o[10] = (syndrome_o == 8'h85) ^ d_i[10];
  assign d_o[11] = (syndrome_o == 8'h19) ^ d_i[11];
  assign d_o[12] = (syndrome_o == 8'h29) ^ d_i[12];
  assign d_o[13] = (syndrome_o == 8'h49) ^ d_i[13];
  assign d_o[14] = (syndrome_o == 8'h89) ^ d_i[14];
  assign d_o[15] = (syndrome_o == 8'h31) ^ d_i[15];
  assign d_o[16] = (syndrome_o == 8'h51) ^ d_i[16];
  assign d_o[17] = (syndrome_o == 8'h91) ^ d_i[17];
  assign d_o[18] = (syndrome_o == 8'h61) ^ d_i[18];
  assign d_o[19] = (syndrome_o == 8'ha1) ^ d_i[19];
  assign d_o[20] = (syndrome_o == 8'hc1) ^ d_i[20];
  assign d_o[21] = (syndrome_o == 8'he) ^ d_i[21];
  assign d_o[22] = (syndrome_o == 8'h16) ^ d_i[22];
  assign d_o[23] = (syndrome_o == 8'h26) ^ d_i[23];
  assign d_o[24] = (syndrome_o == 8'h46) ^ d_i[24];
  assign d_o[25] = (syndrome_o == 8'h86) ^ d_i[25];
  assign d_o[26] = (syndrome_o == 8'h1a) ^ d_i[26];
  assign d_o[27] = (syndrome_o == 8'h2a) ^ d_i[27];
  assign d_o[28] = (syndrome_o == 8'h4a) ^ d_i[28];
  assign d_o[29] = (syndrome_o == 8'h8a) ^ d_i[29];
  assign d_o[30] = (syndrome_o == 8'h32) ^ d_i[30];
  assign d_o[31] = (syndrome_o == 8'h52) ^ d_i[31];
  assign d_o[32] = (syndrome_o == 8'h92) ^ d_i[32];
  assign d_o[33] = (syndrome_o == 8'h62) ^ d_i[33];
  assign d_o[34] = (syndrome_o == 8'ha2) ^ d_i[34];
  assign d_o[35] = (syndrome_o == 8'hc2) ^ d_i[35];
  assign d_o[36] = (syndrome_o == 8'h1c) ^ d_i[36];
  assign d_o[37] = (syndrome_o == 8'h2c) ^ d_i[37];
  assign d_o[38] = (syndrome_o == 8'h4c) ^ d_i[38];
  assign d_o[39] = (syndrome_o == 8'h8c) ^ d_i[39];
  assign d_o[40] = (syndrome_o == 8'h34) ^ d_i[40];
  assign d_o[41] = (syndrome_o == 8'h54) ^ d_i[41];
  assign d_o[42] = (syndrome_o == 8'h94) ^ d_i[42];
  assign d_o[43] = (syndrome_o == 8'h64) ^ d_i[43];
  assign d_o[44] = (syndrome_o == 8'ha4) ^ d_i[44];
  assign d_o[45] = (syndrome_o == 8'hc4) ^ d_i[45];
  assign d_o[46] = (syndrome_o == 8'h38) ^ d_i[46];
  assign d_o[47] = (syndrome_o == 8'h58) ^ d_i[47];
  assign d_o[48] = (syndrome_o == 8'h98) ^ d_i[48];
  assign d_o[49] = (syndrome_o == 8'h68) ^ d_i[49];
  assign d_o[50] = (syndrome_o == 8'ha8) ^ d_i[50];
  assign d_o[51] = (syndrome_o == 8'hc8) ^ d_i[51];
  assign d_o[52] = (syndrome_o == 8'h70) ^ d_i[52];
  assign d_o[53] = (syndrome_o == 8'hb0) ^ d_i[53];
  assign d_o[54] = (syndrome_o == 8'hd0) ^ d_i[54];
  assign d_o[55] = (syndrome_o == 8'he0) ^ d_i[55];
  assign d_o[56] = (syndrome_o == 8'hce) ^ d_i[56];
  assign d_o[57] = (syndrome_o == 8'hf4) ^ d_i[57];
  assign d_o[58] = (syndrome_o == 8'hb6) ^ d_i[58];
  assign d_o[59] = (syndrome_o == 8'h37) ^ d_i[59];
  assign d_o[60] = (syndrome_o == 8'h6b) ^ d_i[60];
  assign d_o[61] = (syndrome_o == 8'hb9) ^ d_i[61];
  assign d_o[62] = (syndrome_o == 8'hd9) ^ d_i[62];
  assign d_o[63] = (syndrome_o == 8'h4f) ^ d_i[63];
  assign d_o[64] = (syndrome_o == 8'h1) ^ d_i[64];
  assign d_o[65] = (syndrome_o == 8'h2) ^ d_i[65];
  assign d_o[66] = (syndrome_o == 8'h4) ^ d_i[66];
  assign d_o[67] = (syndrome_o == 8'h8) ^ d_i[67];
  assign d_o[68] = (syndrome_o == 8'h10) ^ d_i[68];
  assign d_o[69] = (syndrome_o == 8'h20) ^ d_i[69];
  assign d_o[70] = (syndrome_o == 8'h40) ^ d_i[70];
  assign d_o[71] = (syndrome_o == 8'h80) ^ d_i[71];

  // err_o calc. bit0: single error, bit1: double error
  assign single_error = ^syndrome_o;
  assign err_o[0] = single_error;
  assign err_o[1] = ~single_error & (|syndrome_o);

endmodule : prim_secded_72_64_cor
