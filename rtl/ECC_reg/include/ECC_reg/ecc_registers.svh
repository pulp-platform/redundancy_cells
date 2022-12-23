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

`ifndef REDUNDANCY_CELLS_ECC_REGISTERS_SVH_
`define REDUNDANCY_CELLS_ECC_REGISTERS_SVH_

`include "common_cells/registers.svh"

/*******************************************
 *  Building Blocks for Macro definitions  *
 *******************************************/

// Basic module definitions
`define ECC_REGISTER_HEADER ecc_reg #(
`define ECC_REGISTER_BODY(__name) ) __name (
`define ECC_REGISTER_FOOTER );

// Parameter definitions
`define ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC) \
  .DataWidth         (__WIDTH),                     \
  .NumErrorDetect    (__ND),                        \
  .NumErrorCorrect   (__NC)
`define ECC_REGISTER_PARAM_MODE(__E, __D, __C)  \
  .Encode            (__E),                     \
  .Decode            (__D),                     \
  .SelfCorrect       (__C)
`define ECC_REGISTER_PARAM_MODE_NONE `ECC_REGISTER_PARAM_MODE(1'b0, 1'b0, 1'b0)
`define ECC_REGISTER_PARAM_MODE_C    `ECC_REGISTER_PARAM_MODE(1'b0, 1'b0, 1'b1)
`define ECC_REGISTER_PARAM_MODE_D    `ECC_REGISTER_PARAM_MODE(1'b0, 1'b1, 1'b0)
`define ECC_REGISTER_PARAM_MODE_DC   `ECC_REGISTER_PARAM_MODE(1'b0, 1'b1, 1'b1)
`define ECC_REGISTER_PARAM_MODE_E    `ECC_REGISTER_PARAM_MODE(1'b1, 1'b0, 1'b0)
`define ECC_REGISTER_PARAM_MODE_EC   `ECC_REGISTER_PARAM_MODE(1'b1, 1'b0, 1'b1)
`define ECC_REGISTER_PARAM_MODE_ED   `ECC_REGISTER_PARAM_MODE(1'b1, 1'b1, 1'b0)
`define ECC_REGISTER_PARAM_MODE_EDC  `ECC_REGISTER_PARAM_MODE(1'b1, 1'b1, 1'b1)
`define ECC_REGISTER_PARAM_FF_TYPE(__HasReset, __Async, __ActiveLow, __HasLoad) \
  .HasReset          (__HasReset ),    \
  .AsynchronousReset (__Async    ),    \
  .ActiveLowReset    (__ActiveLow),    \
  .HasLoad           (__HasLoad  )
`define ECC_REGISTER_PARAM_FF_TYPE_DEFAULT `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b1, 1'b1, 1'b0)
`define ECC_REGISTER_PARAM_FF_TYPE_AR      `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b1, 1'b0, 1'b0)
`define ECC_REGISTER_PARAM_FF_TYPE_SR      `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b0, 1'b0, 1'b0)
`define ECC_REGISTER_PARAM_FF_TYPE_SRN     `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b0, 1'b1, 1'b0)
`define ECC_REGISTER_PARAM_FF_TYPE_NR      `ECC_REGISTER_PARAM_FF_TYPE(1'b0, 1'b0, 1'b0, 1'b0)
`define ECC_REGISTER_PARAM_FF_TYPE_LARN    `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b1, 1'b1, 1'b1)
`define ECC_REGISTER_PARAM_FF_TYPE_LAR     `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b1, 1'b0, 1'b1)
`define ECC_REGISTER_PARAM_FF_TYPE_LSR     `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b0, 1'b0, 1'b1)
`define ECC_REGISTER_PARAM_FF_TYPE_LSRN    `ECC_REGISTER_PARAM_FF_TYPE(1'b1, 1'b0, 1'b1, 1'b1)
`define ECC_REGISTER_PARAM_FF_TYPE_LNR     `ECC_REGISTER_PARAM_FF_TYPE(1'b0, 1'b0, 1'b0, 1'b1)

`define ECC_REGISTER_PORTS_CLK_ARSTN(__clk,__arst_n)      \
  .clk_i                 (__clk),                         \
  .rst_ni                (__arst_n)
`define ECC_REGISTER_PORTS_CLK_ARST(__clk,__arst)         \
  .clk_i                 (__clk),                         \
  .rst_ni                (~__arst)
`define ECC_REGISTER_PORTS_CLK_SRSTN(__clk,__reset_n_clk) \
  .clk_i                 (__clk),                         \
  .rst_ni                (__reset_n_clk)
`define ECC_REGISTER_PORTS_CLK_SRST(__clk,__reset_clk)    \
  .clk_i                 (__clk),                         \
  .rst_ni                (~__reset_clk)
`define ECC_REGISTER_PORTS_CLK(__clk)                     \
  .clk_i                 (__clk),                         \
  .rst_ni                (1'b1)
`define ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc) \
  .data_i                (__i),                              \
  .data_o                (__o),                              \
  .error_correctable_o   (__ec),                             \
  .error_uncorrectable_o (__enc)
`define ECC_REGISTER_PORTS_LOAD(__load) \
  .load_en_i             (__load)
`define ECC_REGISTER_PORTS_NOLOAD `ECC_REGISTER_PORTS_LOAD(1'b0)

/***********************************************************************
 *  ALL FF Types with no Encoding, no Decoding and no Self-Correction  *
 ***********************************************************************/

// ECC protected Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n)  \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_NONE,                                                      \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                                 \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER


// ECC protected Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)    \
`ECC_REGISTER_HEADER                                                                  \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                         \
`ECC_REGISTER_PARAM_MODE_NONE,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                        \
`ECC_REGISTER_BODY(__name)                                                            \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                          \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                \
`ECC_REGISTER_PORTS_NOLOAD                                                            \
`ECC_REGISTER_FOOTER

// ECC protected Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk)  \
`ECC_REGISTER_HEADER                                                                     \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                            \
`ECC_REGISTER_PARAM_MODE_NONE,                                                           \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                           \
`ECC_REGISTER_BODY(__name)                                                               \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                   \
`ECC_REGISTER_PORTS_NOLOAD                                                               \
`ECC_REGISTER_FOOTER

// ECC protected Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk)  \
`ECC_REGISTER_HEADER                                                                        \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                               \
`ECC_REGISTER_PARAM_MODE_NONE,                                                              \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                  \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                      \
`ECC_REGISTER_PORTS_NOLOAD                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk)          \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_NONE,                                                      \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                                      \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n)  \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_NONE,                                                               \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                              \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst)  \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_NONE,                                                               \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                              \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk)  \
`ECC_REGISTER_HEADER                                                                              \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                     \
`ECC_REGISTER_PARAM_MODE_NONE,                                                                    \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                                   \
`ECC_REGISTER_BODY(__name)                                                                        \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                            \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk)  \
`ECC_REGISTER_HEADER                                                                                 \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                        \
`ECC_REGISTER_PARAM_MODE_NONE,                                                                       \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                                     \
`ECC_REGISTER_BODY(__name)                                                                           \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                     \
`ECC_REGISTER_FOOTER

// ECC protected Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
`define FFLNRECC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk) \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_NONE,                                                      \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_LOAD(__load)                                                    \
`ECC_REGISTER_FOOTER

/********************************************************************
 *  ALL FF Types with Encoding, no Decoding and no Self-Correction  *
 ********************************************************************/

// ECC protected encoding Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n)  \
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_E,                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                         \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_NOLOAD                                                  \
`ECC_REGISTER_FOOTER


// ECC protected encoding Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)    \
`ECC_REGISTER_HEADER                                                          \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                              \
`ECC_REGISTER_PARAM_MODE_E,                                                   \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                \
`ECC_REGISTER_BODY(__name)                                                    \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                  \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                        \
`ECC_REGISTER_PORTS_NOLOAD                                                    \
`ECC_REGISTER_FOOTER

// ECC protected encoding Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk)  \
`ECC_REGISTER_HEADER                                                             \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                 \
`ECC_REGISTER_PARAM_MODE_E,                                                      \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                   \
`ECC_REGISTER_BODY(__name)                                                       \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                           \
`ECC_REGISTER_PORTS_NOLOAD                                                       \
`ECC_REGISTER_FOOTER

// ECC protected encoding Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk)  \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                    \
`ECC_REGISTER_PARAM_MODE_E,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __clk)   \
`ECC_REGISTER_HEADER                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                     \
`ECC_REGISTER_PARAM_MODE_E,                                          \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                       \
`ECC_REGISTER_BODY(__name)                                           \
`ECC_REGISTER_PORTS_CLK(__clk),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),               \
`ECC_REGISTER_PORTS_NOLOAD                                           \
`ECC_REGISTER_FOOTER

// ECC protected encoding Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n)  \
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_E,                                                          \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                     \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst)  \
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_E,                                                          \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                      \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk)  \
`ECC_REGISTER_HEADER                                                                      \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                          \
`ECC_REGISTER_PARAM_MODE_E,                                                               \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                           \
`ECC_REGISTER_BODY(__name)                                                                \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                    \
`ECC_REGISTER_PORTS_LOAD(__load)                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCE(__name, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk)  \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                             \
`ECC_REGISTER_PARAM_MODE_E,                                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected encoding Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
`define FFLNRECCE(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk) \
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_E,                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                             \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK(__clk),                                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_LOAD(__load)                                            \
`ECC_REGISTER_FOOTER

/***********************************************************************
 *  ALL FF Types with no Encoding, Decoding and no Self-Correction     *
 ***********************************************************************/

// ECC protected decoding Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_D,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                                 \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER


// ECC protected decoding Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)   \
`ECC_REGISTER_HEADER                                                                  \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                         \
`ECC_REGISTER_PARAM_MODE_D,                                                           \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                        \
`ECC_REGISTER_BODY(__name)                                                            \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                          \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                \
`ECC_REGISTER_PORTS_NOLOAD                                                            \
`ECC_REGISTER_FOOTER

// ECC protected decoding Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                                     \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                            \
`ECC_REGISTER_PARAM_MODE_D,                                                              \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                           \
`ECC_REGISTER_BODY(__name)                                                               \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                   \
`ECC_REGISTER_PORTS_NOLOAD                                                               \
`ECC_REGISTER_FOOTER

// ECC protected decoding Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                        \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                               \
`ECC_REGISTER_PARAM_MODE_D,                                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                  \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                      \
`ECC_REGISTER_PORTS_NOLOAD                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected decoding Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk)         \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_D,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                                      \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected decoding Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_D,                                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                              \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected decoding Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst) \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_D,                                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                              \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected decoding Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                                              \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                     \
`ECC_REGISTER_PARAM_MODE_D,                                                                       \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                                   \
`ECC_REGISTER_BODY(__name)                                                                        \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                            \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected decoding Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                                 \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                        \
`ECC_REGISTER_PARAM_MODE_D,                                                                          \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                                     \
`ECC_REGISTER_BODY(__name)                                                                           \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                     \
`ECC_REGISTER_FOOTER

// ECC protected decoding Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
`define FFLNRECCD(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk)\
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_D,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_LOAD(__load)                                                    \
`ECC_REGISTER_FOOTER

/********************************************************************
 *  ALL FF Types with Encoding, Decoding and no Self-Correction     *
 ********************************************************************/

// ECC protected encoding and decoding Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_ED,                                                \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                         \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_NOLOAD                                                  \
`ECC_REGISTER_FOOTER


// ECC protected encoding and decoding Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)   \
`ECC_REGISTER_HEADER                                                          \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                              \
`ECC_REGISTER_PARAM_MODE_ED,                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                \
`ECC_REGISTER_BODY(__name)                                                    \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                  \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                        \
`ECC_REGISTER_PORTS_NOLOAD                                                    \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                             \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                 \
`ECC_REGISTER_PARAM_MODE_ED,                                                     \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                   \
`ECC_REGISTER_BODY(__name)                                                       \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                           \
`ECC_REGISTER_PORTS_NOLOAD                                                       \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                    \
`ECC_REGISTER_PARAM_MODE_ED,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __clk)  \
`ECC_REGISTER_HEADER                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                     \
`ECC_REGISTER_PARAM_MODE_ED,                                         \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                       \
`ECC_REGISTER_BODY(__name)                                           \
`ECC_REGISTER_PORTS_CLK(__clk),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),               \
`ECC_REGISTER_PORTS_NOLOAD                                           \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_ED,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                     \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst) \
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_ED,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                      \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                                      \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                          \
`ECC_REGISTER_PARAM_MODE_ED,                                                              \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                           \
`ECC_REGISTER_BODY(__name)                                                                \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                    \
`ECC_REGISTER_PORTS_LOAD(__load)                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCED(__name, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                             \
`ECC_REGISTER_PARAM_MODE_ED,                                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected encoding and decoding Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
`define FFLNRECCED(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk)\
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_ED,                                                \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                             \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK(__clk),                                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_LOAD(__load)                                            \
`ECC_REGISTER_FOOTER

/***********************************************************************
 *  ALL FF Types with no Encoding, no Decoding and Self-Correction     *
 ***********************************************************************/

// ECC protected self-correcting Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_C,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                                 \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER


// ECC protected self-correcting Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)   \
`ECC_REGISTER_HEADER                                                                  \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                         \
`ECC_REGISTER_PARAM_MODE_C,                                                           \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                        \
`ECC_REGISTER_BODY(__name)                                                            \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                          \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                \
`ECC_REGISTER_PORTS_NOLOAD                                                            \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                                     \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                            \
`ECC_REGISTER_PARAM_MODE_C,                                                              \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                           \
`ECC_REGISTER_BODY(__name)                                                               \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                   \
`ECC_REGISTER_PORTS_NOLOAD                                                               \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                        \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                               \
`ECC_REGISTER_PARAM_MODE_C,                                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                  \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                      \
`ECC_REGISTER_PORTS_NOLOAD                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk)         \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_C,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                                      \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_C,                                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                              \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst) \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_C,                                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                              \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                                              \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                     \
`ECC_REGISTER_PARAM_MODE_C,                                                                       \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                                   \
`ECC_REGISTER_BODY(__name)                                                                        \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                            \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                                 \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                        \
`ECC_REGISTER_PARAM_MODE_C,                                                                          \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                                     \
`ECC_REGISTER_BODY(__name)                                                                           \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                     \
`ECC_REGISTER_FOOTER

// ECC protected self-correcting Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
`define FFLNRECCC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk)\
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_C,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_LOAD(__load)                                                    \
`ECC_REGISTER_FOOTER

/********************************************************************
 *  ALL FF Types with Encoding, no Decoding and Self-Correction     *
 ********************************************************************/

// ECC protected encoding and self-correcting Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_EC,                                                \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                         \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_NOLOAD                                                  \
`ECC_REGISTER_FOOTER


// ECC protected encoding and self-correcting Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)   \
`ECC_REGISTER_HEADER                                                          \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                              \
`ECC_REGISTER_PARAM_MODE_EC,                                                  \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                \
`ECC_REGISTER_BODY(__name)                                                    \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                  \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                        \
`ECC_REGISTER_PORTS_NOLOAD                                                    \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                             \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                 \
`ECC_REGISTER_PARAM_MODE_EC,                                                     \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                   \
`ECC_REGISTER_BODY(__name)                                                       \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                           \
`ECC_REGISTER_PORTS_NOLOAD                                                       \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                    \
`ECC_REGISTER_PARAM_MODE_EC,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk)  \
`ECC_REGISTER_HEADER                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                     \
`ECC_REGISTER_PARAM_MODE_EC,                                         \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                       \
`ECC_REGISTER_BODY(__name)                                           \
`ECC_REGISTER_PORTS_CLK(__clk),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),               \
`ECC_REGISTER_PORTS_NOLOAD                                           \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n) \
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_EC,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                     \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst) \
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_EC,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                      \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk) \
`ECC_REGISTER_HEADER                                                                      \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                          \
`ECC_REGISTER_PARAM_MODE_EC,                                                              \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                           \
`ECC_REGISTER_BODY(__name)                                                                \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                    \
`ECC_REGISTER_PORTS_LOAD(__load)                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCEC(__name, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk) \
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                             \
`ECC_REGISTER_PARAM_MODE_EC,                                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected encoding and self-correcting Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is not corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
`define FFLNRECCEC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk)\
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_EC,                                                \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                             \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK(__clk),                                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_LOAD(__load)                                            \
`ECC_REGISTER_FOOTER

/***********************************************************************
 *  ALL FF Types with no Encoding, Decoding and Self-Correction        *
 ***********************************************************************/

// ECC protected decoding and self-correcting Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n)\
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_DC,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                                 \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER


// ECC protected decoding and self-correcting Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)  \
`ECC_REGISTER_HEADER                                                                  \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                         \
`ECC_REGISTER_PARAM_MODE_DC,                                                          \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                        \
`ECC_REGISTER_BODY(__name)                                                            \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                          \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                \
`ECC_REGISTER_PORTS_NOLOAD                                                            \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk)\
`ECC_REGISTER_HEADER                                                                     \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                            \
`ECC_REGISTER_PARAM_MODE_DC,                                                             \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                           \
`ECC_REGISTER_BODY(__name)                                                               \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                   \
`ECC_REGISTER_PORTS_NOLOAD                                                               \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk)\
`ECC_REGISTER_HEADER                                                                        \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                               \
`ECC_REGISTER_PARAM_MODE_DC,                                                                \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                  \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                        \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                      \
`ECC_REGISTER_PORTS_NOLOAD                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __clk)        \
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                       \
`ECC_REGISTER_PARAM_MODE_DC,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                                      \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK(__clk),                                                     \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n)\
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_DC,                                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                              \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst)\
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                \
`ECC_REGISTER_PARAM_MODE_DC,                                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                              \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk)\
`ECC_REGISTER_HEADER                                                                              \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                     \
`ECC_REGISTER_PARAM_MODE_DC,                                                                      \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                                   \
`ECC_REGISTER_BODY(__name)                                                                        \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                            \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                  \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk)\
`ECC_REGISTER_HEADER                                                                                 \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                                        \
`ECC_REGISTER_PARAM_MODE_DC,                                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                                     \
`ECC_REGISTER_BODY(__name)                                                                           \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                                 \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                                     \
`ECC_REGISTER_FOOTER

// ECC protected decoding and self-correcting Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __WIDTH: width of the data, in bits
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs). Data must already be ECC encoded.
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: load __i value into FF
// __clk: clock input
`define FFLNRECCDC(__name, __WIDTH, __ND, __NC, __i, __o, __ec, __enc, __load, __clk)\
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC(__WIDTH, __ND, __NC),                                        \
`ECC_REGISTER_PARAM_MODE_DC,                                                         \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                                      \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK(__clk),                                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

/********************************************************************
 *  ALL FF Types with Encoding, Decoding and Self-Correction        *
 ********************************************************************/

// ECC protected encoding, decoding and self-correcting Flip-Flop with asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst_n)\
`ECC_REGISTER_HEADER                                                        \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                            \
`ECC_REGISTER_PARAM_MODE_EDC,                                               \
`ECC_REGISTER_PARAM_FF_TYPE_DEFAULT                                         \
`ECC_REGISTER_BODY(__name)                                                  \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                             \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                      \
`ECC_REGISTER_PORTS_NOLOAD                                                  \
`ECC_REGISTER_FOOTER


// ECC protected encoding, decoding and self-correcting Flip-Flop with asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __arst)  \
`ECC_REGISTER_HEADER                                                          \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                              \
`ECC_REGISTER_PARAM_MODE_EDC,                                                 \
`ECC_REGISTER_PARAM_FF_TYPE_AR                                                \
`ECC_REGISTER_BODY(__name)                                                    \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                  \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                        \
`ECC_REGISTER_PORTS_NOLOAD                                                    \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Flip-Flop with synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_clk)\
`ECC_REGISTER_HEADER                                                             \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                 \
`ECC_REGISTER_PARAM_MODE_EDC,                                                    \
`ECC_REGISTER_PARAM_FF_TYPE_SR                                                   \
`ECC_REGISTER_BODY(__name)                                                       \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                           \
`ECC_REGISTER_PORTS_NOLOAD                                                       \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Flip-Flop with synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk, __reset_n_clk)\
`ECC_REGISTER_HEADER                                                                \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                    \
`ECC_REGISTER_PARAM_MODE_EDC,                                                       \
`ECC_REGISTER_PARAM_FF_TYPE_SRN                                                     \
`ECC_REGISTER_BODY(__name)                                                          \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                              \
`ECC_REGISTER_PORTS_NOLOAD                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Always-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
//      Note: Input Data is not saved while FF is self-correcting (__ec high)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __clk: clock input
`define FFNRECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __clk) \
`ECC_REGISTER_HEADER                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                     \
`ECC_REGISTER_PARAM_MODE_EDC,                                        \
`ECC_REGISTER_PARAM_FF_TYPE_NR                                       \
`ECC_REGISTER_BODY(__name)                                           \
`ECC_REGISTER_PORTS_CLK(__clk),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),               \
`ECC_REGISTER_PORTS_NOLOAD                                           \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst_n)\
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_EDC,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_LARN                                                     \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARSTN(__clk, __arst_n),                                      \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __arst)\
`ECC_REGISTER_HEADER                                                                 \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                     \
`ECC_REGISTER_PARAM_MODE_EDC,                                                        \
`ECC_REGISTER_PARAM_FF_TYPE_LAR                                                      \
`ECC_REGISTER_BODY(__name)                                                           \
`ECC_REGISTER_PORTS_CLK_ARST(__clk, __arst),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                               \
`ECC_REGISTER_PORTS_LOAD(__load)                                                     \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk, __reset_clk)\
`ECC_REGISTER_HEADER                                                                      \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                          \
`ECC_REGISTER_PARAM_MODE_EDC,                                                             \
`ECC_REGISTER_PARAM_FF_TYPE_LSR                                                           \
`ECC_REGISTER_BODY(__name)                                                                \
`ECC_REGISTER_PORTS_CLK_SRST(__clk, __reset_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                    \
`ECC_REGISTER_PORTS_LOAD(__load)                                                          \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc,__load,  __clk, __reset_n_clk)\
`ECC_REGISTER_HEADER                                                                         \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                                             \
`ECC_REGISTER_PARAM_MODE_EDC,                                                                \
`ECC_REGISTER_PARAM_FF_TYPE_LSRN                                                             \
`ECC_REGISTER_BODY(__name)                                                                   \
`ECC_REGISTER_PORTS_CLK_SRSTN(__clk, __reset_n_clk),                                         \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                                             \
`ECC_REGISTER_FOOTER

// ECC protected encoding, decoding and self-correcting Load-enable Flip-Flop without reset
// __name: Name of the ECC FF instance
// __ND: Number of errors the used code can detect
// __NC: Number of errors the used code can correct
// __i: data input (replaces D input for normal FFs)
// __o: data output (replaces Q output for normal FFs). Contains ECC bits and is corrected.
// __ec: error correctable output. if 1, detection unit found a correctable error
// __enc: error not correctable output. if 1, detection unit found an uncorrrectable error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
`define FFLNRECCEDC(__name, __ND, __NC, __i, __o, __ec, __enc, __load, __clk)\
`ECC_REGISTER_HEADER                                                         \
`ECC_REGISTER_PARAM_ECC($bits(__i), __ND, __NC),                             \
`ECC_REGISTER_PARAM_MODE_EDC,                                                \
`ECC_REGISTER_PARAM_FF_TYPE_LNR                                              \
`ECC_REGISTER_BODY(__name)                                                   \
`ECC_REGISTER_PORTS_CLK(__clk),                                              \
`ECC_REGISTER_PORTS_DATA_ERROR(__i, __o, __ec, __enc),                       \
`ECC_REGISTER_PORTS_LOAD(__load)                                             \
`ECC_REGISTER_FOOTER

`endif