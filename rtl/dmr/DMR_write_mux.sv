// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Description: This module is used to apply DMR to the following circuit:
//              A Table of N Elements of M bits each, where only one element
//              can be written at the time.
//              The DMR write protection uses two write-data (M bits each) and
//              two write-enable inputs (N bits each). These signals are
//              supposed to be generated independently (DMR).
//              The 'dmr_error_o' signal indicates if there is a mismatch in the
//              write-data or the write-enable data between the two inputs.
//              The 'write_i' signal controls if the write is executed. This
//              signal is supposed to be a combination of the 'dmr_error_o'
//              signal and other error signals. It can also be used to force a
//              write when DMR checking is to be disabled. When writing is
//              forced, the data in we signals from port 1 are used.

// Vulnerability to Single Event Transients (SETs):
// This module is designed to protect a design against single event transients.
// While this module is designed to protect agains SETs occuring in the
// combinatorial logic that generate the write-data and write-enable signals,
// it still has some internal vulnerabilities:
//  - The AND gates that check the write-enable signals (including any buffers
//    in the 'write_i' signal and at the output of the AND gates) are vulnerable
//    to SETs. This cannot be prevented, as a single error signal needs to
//    influence M*N MUX2 gates and this large fan-out requires buffers to be
//    inserted, which in turn are vulnerable to SETs.
//  - The MUXes that control the data flow (and all buffers on the incomming
//    signals) are also vulnerable to SETs if the data is not encoded.
//    Using Single Error Correction (SEC) encoded data (e.g. Hamming code or
//    TMR) offers an easy way to protect the data path and the MUXes agains SETs.
// This module offers a trade-off between Area-overhead and vulnerability.
// The vulnerability could be reduced by applying TMR to the 'write_i' tree,
// and voting every single of the N*M MUX2 control signals.

module DMR_write_mux #(
  parameter type         data_t       = logic,
  parameter int unsigned NumDataItems = 1
) (
  // Data Ports
  input  data_t [NumDataItems-1:0] data_i,
  output data_t [NumDataItems-1:0] data_o,
  // Write Ports
  input  data_t                    wdata_1_i,
  input  data_t                    wdata_2_i,
  input  logic  [NumDataItems-1:0] wen_1_i,
  input  logic  [NumDataItems-1:0] wen_2_i,
  // Error & Control Signals
  output logic                     dmr_error_o,
  input  logic                     write_i
);

// Internal signals
logic                     wdata_error, wen_error;
logic  [NumDataItems-1:0] wen;
data_t [NumDataItems-1:0] wdata_expanded;

// Error checking
assign wdata_error = (wdata_1_i != wdata_2_i);
assign wen_error   = (wen_1_i   != wen_2_i);
assign dmr_error_o = wdata_error | wen_error;

// Write signal masking (Vulnerable)
assign wen = wen_1_i & {NumDataItems{write_i}};

// Input signal distribution (Vulnerable if not ECC protected)
assign wdata_expanded = {NumDataItems{wdata_1_i}};

// Write multiplexing (Vulnerable if not ECC protected)
for (genvar i = 0; i < NumDataItems; i++) begin
  assign data_o[i] = wen[i] ? wdata_expanded[i] : data_i[i];
end

endmodule
