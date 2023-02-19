// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Luca Rufer (lrufer@student.ethz.ch)

`ifndef REDUNDANCY_CELLS_ECC_CALC_SVH_
`define REDUNDANCY_CELLS_ECC_CALC_SVH_

// Calculate the ECC distance depending on the given parameters
`define ECC_DIST(NumErrorCorrect, NumErrorDetect)                       \
        (((NumErrorCorrect) >= (NumErrorDetect)) ?                      \
          (2 * (NumErrorCorrect) + 1) :                                 \
          ((NumErrorCorrect) + (NumErrorDetect) + 1))

// Calcualte the the number of ECC bits required to encode a given amount
// of data bits with a given code distance
`define ECC_WIDTH(DATA_WIDTH, ECC_DIST)                                 \
 ((ECC_DIST == 0) ? -1 : /* Invalid ECC distance */                     \
  (ECC_DIST == 1) ?  0 : /* No Coding */                                \
  (ECC_DIST == 2) ?  1 : /* Single Parity bit */                        \
  (ECC_DIST == 3) ? (    /* Hamming Code: k <= 2^r - r - 1 */           \
    (DATA_WIDTH <=           0) ? 0 :                                   \
    (DATA_WIDTH <=   4 - 2 - 1) ? 2 :                                   \
    (DATA_WIDTH <=   8 - 3 - 1) ? 3 :                                   \
    (DATA_WIDTH <=  16 - 4 - 1) ? 4 :                                   \
    (DATA_WIDTH <=  32 - 5 - 1) ? 5 :                                   \
    (DATA_WIDTH <=  64 - 6 - 1) ? 6 :                                   \
    (DATA_WIDTH <= 128 - 7 - 1) ? 7 :                                   \
    (DATA_WIDTH <= 256 - 8 - 1) ? 8 :                                   \
    (DATA_WIDTH <= 512 - 9 - 1) ? 9 : -1) :                             \
  (ECC_DIST == 4) ? (     /* Hsiao Code: k <= 2^(r-1) - r */            \
    (DATA_WIDTH <=        0) ?  0 :                                     \
    (DATA_WIDTH <=   4 -  3) ?  3 :                                     \
    (DATA_WIDTH <=   8 -  4) ?  4 :                                     \
    (DATA_WIDTH <=  16 -  5) ?  5 :                                     \
    (DATA_WIDTH <=  32 -  6) ?  6 :                                     \
    (DATA_WIDTH <=  64 -  7) ?  7 :                                     \
    (DATA_WIDTH <= 128 -  8) ?  8 :                                     \
    (DATA_WIDTH <= 256 -  9) ?  9 :                                     \
    (DATA_WIDTH <= 512 - 10) ? 10 : -1) :                               \
  -1) /* Other Codes not supported */

`endif
