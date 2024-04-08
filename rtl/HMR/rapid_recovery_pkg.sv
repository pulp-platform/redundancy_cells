/* Copyright 2020 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 * 
 * Recovery Region Package
 * 
 */

package rapid_recovery_pkg;

localparam int unsigned DataWidth = 32;
localparam int unsigned ProtectedWidth = 39;
localparam int unsigned RegfileAddr = 6;
localparam int unsigned RecoveryStateBits = 3;
/* CSRs */
localparam int unsigned MstatusWidth = 7;
localparam int unsigned MtvecWidth  = 24;
localparam int unsigned McauseWidth = 6;

typedef struct packed {
  bit ReducedCsrsBackupEnable;
  bit FullCsrsBackupEnable;
  bit IntRegFileBackupEnable;
  bit FpRegFileBackupEnable;
  bit ProgramCounterBackupEnable;
} rapid_recovery_cfg_t;

localparam rapid_recovery_cfg_t RrDefaultCfg = {
  ReducedCsrsBackupEnable: 1,
  FullCsrsBackupEnable: 0,
  IntRegFileBackupEnable: 1,
  FpRegFileBackupEnable: 0,
  ProgramCounterBackupEnable: 1
};

endpackage
