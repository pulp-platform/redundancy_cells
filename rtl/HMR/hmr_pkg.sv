// Copyright 2024 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Hybrid modular redundancy support package

package hmr_pkg;
  function automatic int max(int a, int b);
    return (a > b) ? a : b;
  endfunction

  typedef struct packed {
    logic recovery_start;
    logic rr_enable;
  } rr_ctrl_t;

  typedef struct packed {
    logic recovery_finished;
    logic rr_error;
  } rr_status_t;


endpackage
