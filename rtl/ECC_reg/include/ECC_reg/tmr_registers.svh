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

`ifndef REDUNDANCY_CELLS_TMR_REGISTERS_SVH_
`define REDUNDANCY_CELLS_TMR_REGISTERS_SVH_

// TMR protected Flip-Flop with asynchronous active-low reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFTMR(__name, __i, __rst_val, __o, __error, __clk, __arst_n)          \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b1),                                                  \
  .ActiveLowReset    (1'b1),                                                  \
  .HasLoad           (1'b0)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (__arst_n),                                              \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (1'b0)                                                   \
);


// TMR protected Flip-Flop with asynchronous active-high reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFARTMR(__name, __i, __rst_val, __o, __error, __clk, __arst)          \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b1),                                                  \
  .ActiveLowReset    (1'b0),                                                  \
  .HasLoad           (1'b0)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (~__arst),                                               \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (1'b0)                                                   \
);

// TMR protected Flip-Flop with synchronous active-high reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSRTMR(__name, __i, __rst_val, __o, __error, __clk, __reset_clk)     \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b0),                                                  \
  .ActiveLowReset    (1'b0),                                                  \
  .HasLoad           (1'b0)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (~__reset_clk),                                          \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (1'b0)                                                   \
);

// TMR protected Flip-Flop with synchronous active-low reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRNTMR(__name, __i, __rst_val, __o, __error, __clk, __reset_n_clk)  \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b0),                                                  \
  .ActiveLowReset    (1'b1),                                                  \
  .HasLoad           (1'b0)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (__reset_n_clk),                                         \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (1'b0)                                                   \
);

// TMR protected Always-enable Flip-Flop without reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __clk: clock input
`define FFNRTMR(__name, __i, __o, __error, __clk)                             \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b0),                                                  \
  .AsynchronousReset (1'b1),                                                  \
  .ActiveLowReset    (1'b1),                                                  \
  .HasLoad           (1'b0)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (1'b0),                                                  \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     ('0),                                                    \
  .load_en_i         (1'b0)                                                   \
);

// TMR protected Flip-Flop with load-enable and asynchronous active-low reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLTMR(__name, __i, __rst_val, __o, __error, __load, __clk, __arst_n) \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b1),                                                  \
  .ActiveLowReset    (1'b1),                                                  \
  .HasLoad           (1'b1)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (__arst_n),                                              \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (__load)                                                 \
);

// TMR protected Flip-Flop with load-enable and asynchronous active-high reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLARTMR(__name, __i, __rst_val, __o, __error, __load, __clk, __arst) \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b1),                                                  \
  .ActiveLowReset    (1'b0),                                                  \
  .HasLoad           (1'b1)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (~__arst),                                               \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (__load)                                                 \
);

// TMR protected Flip-Flop with load-enable and synchronous active-high reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSRTMR(__name, __i, __rst_val, __o, __error, __load, __clk, __reset_clk)  \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b0),                                                  \
  .ActiveLowReset    (1'b0),                                                  \
  .HasLoad           (1'b1)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (~__reset_clk),                                          \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (__load)                                                 \
);

// TMR protected Flip-Flop with load-enable and synchronous active-low reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __rst_val: Reset value of the FF.
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRNTMR(__name, __i, __rst_val, __o, __error, __load,  __clk, __reset_n_clk)  \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b1),                                                  \
  .AsynchronousReset (1'b0),                                                  \
  .ActiveLowReset    (1'b1),                                                  \
  .HasLoad           (1'b1)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (__reset_n_clk),                                         \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     (__rst_val),                                             \
  .load_en_i         (__load)                                                 \
);

// TMR protected Load-enable Flip-Flop without reset
// __name: Name of the TMR FF instance
// __i: data input (replaces D input for normal FFs).
// __o: data output (replaces Q output for normal FFs).
// __error: error output. if 1, detection unit found and corrected an error
// __load: encode __i and load it into FF. Otherwise, the old value is kept.
// __clk: clock input
`define FFLNRTMR(__name, __i, __o, __error, __load, __clk)                    \
tmr_reg #(                                                                    \
  .DataWidth         ($bits(__i)),                                            \
  .HasReset          (1'b0),                                                  \
  .AsynchronousReset (1'b1),                                                  \
  .ActiveLowReset    (1'b1),                                                  \
  .HasLoad           (1'b1)                                                   \
) __name (                                                                    \
  .clk_i             (__clk),                                                 \
  .rst_ni            (1'b0),                                                  \
  .data_i            (__i),                                                   \
  .data_o            (__o),                                                   \
  .err_o             (__error),                                               \
  .reset_value_i     ('0),                                                    \
  .load_en_i         (__load)                                                 \
);

`endif
