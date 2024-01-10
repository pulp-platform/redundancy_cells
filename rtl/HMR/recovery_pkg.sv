// Copyright 2023 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Recovery Region Package

package recovery_pkg;

localparam int unsigned DataWidth = 32;
localparam int unsigned RegfileAddr = 6;
localparam int unsigned RecoveryStateBits = 3;

typedef struct packed {
  // Write Port A
  logic                   we_a;
  logic [RegfileAddr-1:0] waddr_a;
  logic [  DataWidth-1:0] wdata_a;
  // Write Port B
  logic                   we_b;
  logic [RegfileAddr-1:0] waddr_b;
  logic [  DataWidth-1:0] wdata_b;
} regfile_write_t;

typedef struct packed {
  logic [RegfileAddr-1:0] raddr_a;
  logic [RegfileAddr-1:0] raddr_b;
} regfile_raddr_t;

typedef struct packed {
  logic [DataWidth-1:0] rdata_a;
  logic [DataWidth-1:0] rdata_b;
} regfile_rdata_t;

typedef enum logic [RecoveryStateBits-1:0]{
  IDLE       ,
  RESET      ,
  HALT_REQ   ,
  HALT_WAIT  ,
  RESTORE_PC ,
  RESTORE_RF ,
  RESTORE_CSR,
  EXIT
} recovery_routine_state_e;

endpackage
