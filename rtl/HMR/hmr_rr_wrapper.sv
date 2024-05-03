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
// Hybrid modular redundancy wrapping unit with rapid recovery

module hmr_rr_wrapper import hmr_pkg::*; #(
  // Wrapper parameters
  /// Number of physical cores
  parameter  int unsigned NumCores       = 0,
  /// Enables support for Dual Modular Redundancy
  parameter  bit          DMRSupported   = 1'b1,
  /// Locks HMR into permanent DMR mode
  parameter  bit          DMRFixed       = 1'b0,
  /// Enables support for Triple Modular Redundancy
  parameter  bit          TMRSupported   = 1'b1,
  /// Locks HMR into permanent TMR mode
  parameter  bit          TMRFixed       = 1'b0,
  /// Interleave DMR/TMR cores, alternatively with sequential grouping
  parameter  bit          InterleaveGrps = 1'b1,
  /// rapid recovery - tbd
  parameter  bit          RapidRecovery  = 1'b0,
  /// Separates voters and checkers for data, which are then only checked if data request is valid
  parameter  bit          SeparateData   = 1'b1,
  /// Number of separate voters/checkers for individual buses
  parameter  int unsigned NumBusVoters   = 1,
  /// Address width of the core register file (in RISC-V it should be always 6)
  parameter  int unsigned RfAddrWidth    = 6,
  parameter  int unsigned SysDataWidth   = 32,
  /// General core inputs wrapping struct
  parameter  type         all_inputs_t = logic,
  /// General core outputs wrapping struct
  parameter  type         nominal_outputs_t = logic,
  /// Cores' backup output bus
  parameter  type         core_backup_t  = logic,
  /// Bus outputs wrapping struct
  parameter  type         bus_outputs_t  = logic,
  parameter  type         reg_req_t      = logic,
  parameter  type         reg_rsp_t      = logic,
  /// Rapid recovery structure
  parameter  type         rapid_recovery_t = logic,
  parameter  type         regfile_write_t  = logic,
  parameter  type         regfile_raddr_t  = logic,
  parameter  type         regfile_rdata_t  = logic,
  parameter  type         csr_intf_t       = logic,
  parameter  type         pc_intf_t        = logic,
  // Local parameters depending on the above ones
  /// Number of TMR groups (virtual TMR cores)
  localparam int unsigned NumTMRGroups   = (TMRFixed || TMRSupported) ? NumCores/3 : 1,
  /// Number of physical cores used for TMR
  localparam int unsigned NumTMRCores    = NumTMRGroups * 3,
  /// Number of physical cores NOT used for TMR
  localparam int unsigned NumTMRLeftover = NumCores - NumTMRCores,
  /// Number of DMR groups (virtual DMR cores)
  localparam int unsigned NumDMRGroups   = (DMRFixed || DMRSupported) ? NumCores/2 : 1,
  /// Nubmer of physical cores used for DMR
  localparam int unsigned NumDMRCores    = NumDMRGroups * 2,
  /// Number of physical cores NOT used for DMR
  localparam int unsigned NumDMRLeftover = NumCores - NumDMRCores,
  /// Number of cores visible to the system (Fixed mode removes unneeded system ports)
  localparam int unsigned NumSysCores    =
    DMRFixed ? NumDMRGroups : TMRFixed ? NumTMRGroups : NumCores,
  /// Number of RapidRecover Units
  localparam int unsigned NumRRUnits =
    max(DMRSupported || DMRFixed ? NumDMRGroups : 0, TMRSupported || TMRFixed ? NumTMRGroups : 0)
) (
  input  logic      clk_i ,
  input  logic      rst_ni,

  // Port to configuration unit
  input  reg_req_t  reg_request_i ,
  output reg_rsp_t  reg_response_o,

  // TMR signals
  output logic [    NumCores-1:0] tmr_core_en_o,
  output logic [NumTMRGroups-1:0] tmr_failure_o    ,
  output logic [    NumCores-1:0] tmr_error_o      ,
  output logic [NumTMRGroups-1:0] tmr_resynch_req_o,
  output logic [    NumCores-1:0] tmr_sw_synch_req_o,
  input  logic [NumTMRGroups-1:0] tmr_cores_synch_i,

  // DMR signals
  output logic [    NumCores-1:0] dmr_core_en_o,
  output logic [NumDMRGroups-1:0] dmr_failure_o    ,
  output logic [NumDMRGroups-1:0] dmr_resynch_req_o,
  output logic [    NumCores-1:0] dmr_sw_synch_req_o,
  input  logic [NumDMRGroups-1:0] dmr_cores_synch_i,

  // Rapid recovery buses
  output rapid_recovery_t [NumSysCores-1:0] rapid_recovery_o,
  input  core_backup_t    [NumCores-1:0]    core_backup_i,

  // Boot address is handled apart from other signals
  input  logic                              [SysDataWidth-1:0] sys_bootaddress_i,
  input  all_inputs_t      [NumSysCores-1:0]                   sys_inputs_i,
  output nominal_outputs_t [NumSysCores-1:0]                   sys_nominal_outputs_o,
  output bus_outputs_t     [NumSysCores-1:0][NumBusVoters-1:0] sys_bus_outputs_o,
  input  logic             [NumSysCores-1:0]                   sys_fetch_en_i,
  input  logic             [NumSysCores-1:0][NumBusVoters-1:0] enable_bus_vote_i,

  // Boot address is handled apart from other signals
  output logic             [NumCores-1:0][SysDataWidth-1:0] core_bootaddress_o,
  output logic             [NumCores-1:0]                   core_setback_o,
  output all_inputs_t      [NumCores-1:0]                   core_inputs_o,
  input  nominal_outputs_t [NumCores-1:0]                   core_nominal_outputs_i,
  input  bus_outputs_t     [NumCores-1:0][NumBusVoters-1:0] core_bus_outputs_i
);

  function automatic int tmr_group_id (int core_id);
    if (InterleaveGrps) return core_id % NumTMRGroups;
    else                return (core_id/3);
  endfunction

  function automatic int tmr_core_id (int group_id, int core_offset);
    if (InterleaveGrps) return group_id + core_offset * NumTMRGroups;
    else                return (group_id * 3) + core_offset;
  endfunction

  function automatic int tmr_shared_id (int group_id);
    if (InterleaveGrps || !(DMRSupported || DMRFixed)) return group_id;
    else                return group_id + group_id/2;
  endfunction

  if (DMRSupported && TMRSupported && RapidRecovery && !InterleaveGrps)
    $warning("TMR and DMR with RR without interleaving groups may lead to malfunctioning RR ",
              "synchronization.");

  function automatic int tmr_offset_id (int core_id);
    if (InterleaveGrps) return core_id / NumTMRGroups;
    else                return core_id % 3;
  endfunction

  function automatic int dmr_group_id (int core_id);
    if (InterleaveGrps) return core_id % NumDMRGroups;
    else                return (core_id/2);
  endfunction

  function automatic int dmr_core_id (int group_id, int core_offset);
    if (InterleaveGrps) return group_id + core_offset * NumDMRGroups;
    else                return (group_id * 2) + core_offset;
  endfunction

  function automatic int dmr_shared_id (int group_id);
    return group_id;
  endfunction

  function automatic int dmr_offset_id (int core_id);
    if (InterleaveGrps) return core_id / NumDMRGroups;
    else                return core_id % 2;
  endfunction

  logic [NumDMRGroups-1:0] dmr_failure_hmr, dmr_failure_rr;
  logic [NumTMRGroups-1:0] tmr_failure_hmr, tmr_failure_rr;
  logic [    NumCores-1:0] tmr_error_hmr;
  logic [NumTMRGroups-1:0][2:0] tmr_error_rr;
  logic [NumCores-1:0] hmr_setback;

  rr_ctrl_t   [NumRRUnits-1:0] rr_ctrl;
  rr_status_t [NumRRUnits-1:0] rr_status;

  hmr_unit #(
    .NumCores         ( NumCores          ),
    .DMRSupported     ( DMRSupported      ),
    .DMRFixed         ( DMRFixed          ),
    .TMRSupported     ( TMRSupported      ),
    .TMRFixed         ( TMRFixed          ),
    .InterleaveGrps   ( InterleaveGrps    ),
    .SeparateData     ( SeparateData      ),
    .NumBusVoters     ( NumBusVoters      ),
    .all_inputs_t     ( all_inputs_t      ),
    .nominal_outputs_t( nominal_outputs_t ),
    .bus_outputs_t    ( bus_outputs_t     ),
    .reg_req_t        ( reg_req_t         ),
    .reg_rsp_t        ( reg_rsp_t         )
  ) i_hmr (
    .clk_i,
    .rst_ni,

    .reg_request_i          (),
    .reg_response_o         (),

    .tmr_core_en_o,
    .tmr_failure_o          ( tmr_failure_hmr ),
    .tmr_error_o            ( tmr_error_hmr ),
    .tmr_resynch_req_o,
    .tmr_sw_synch_req_o,
    .tmr_cores_synch_i,

    .dmr_core_en_o,
    .dmr_failure_o          ( dmr_failure_hmr ),
    .dmr_resynch_req_o,
    .dmr_sw_synch_req_o,
    .dmr_cores_synch_i,

    .rr_ctrl_o              ( rr_ctrl ),
    .rr_status_i            ( rr_status ),

    .sys_inputs_i,
    .sys_nominal_outputs_o,
    .sys_bus_outputs_o,
    .sys_fetch_en_i,
    .enable_bus_vote_i,

    .core_setback_o         ( hmr_setback ),
    .core_inputs_o,
    .core_nominal_outputs_i,
    .core_bus_outputs_i
  );

  core_backup_t     [ NumDMRGroups-1:0] dmr_backup_outputs;
  core_backup_t     [ NumTMRGroups-1:0] tmr_backup_outputs;
  // logic             [ NumDMRGroups-1:0][SysDataWidth-1:0] checkpoint_reg_q;

  logic             [ NumDMRGroups-1:0] dmr_recovery_start, dmr_recovery_finished;
  logic             [ NumTMRGroups-1:0] tmr_recovery_start, tmr_recovery_finished;
  logic             [NumRRUnits-1:0] rapid_recovery_start, rapid_recovery_finished;
  logic             [NumRRUnits-1:0] rapid_recovery_backup_en_inp, rapid_recovery_backup_en_oup;
  logic             [NumRRUnits-1:0] rapid_recovery_setback;
  rapid_recovery_t  [NumRRUnits-1:0] rapid_recovery_bus;
  core_backup_t     [NumRRUnits-1:0] rapid_recovery_backup_bus;
  nominal_outputs_t [NumRRUnits-1:0] rapid_recovery_nominal;

  if (RapidRecovery) begin : gen_rapid_recovery_hw
    if (DMRSupported) begin : gen_dmr_rr
      for (genvar i = 0; i < NumDMRGroups; i++) begin : gen_dmr_rr
        DMR_checker #(
          .DataWidth( $bits(core_backup_t) ),
          .Pipeline ( 1                    )
        ) i_dmr_core_checker_backup (
          .clk_i,
          .rst_ni,

          .inp_a_i( core_backup_i [dmr_core_id(i, 0)] ),
          .inp_b_i( core_backup_i [dmr_core_id(i, 1)] ),
          .check_o( dmr_backup_outputs [       i    ] ),
          .error_o( dmr_failure_rr     [       i    ] )
        );
        assign dmr_failure_o[i] = (dmr_core_en_o[dmr_core_id(i, 0)] &&
                                   rr_ctrl[dmr_shared_id(i)].rr_enable) ?
                                  dmr_failure_hmr[i] | dmr_failure_rr[i] :
                                  dmr_failure_hmr[i];
      end
    end else begin : gen_no_dmr_rr
      assign dmr_backup_outputs = '0;
      assign dmr_failure_rr     = '0;
      assign dmr_failure_o      = dmr_failure_hmr;
    end
    if (TMRSupported) begin : gen_tmr_rr
      for (genvar i = 0; i < NumTMRGroups; i++) begin : gen_tmr_rr
        bitwise_TMR_voter #(
          .DataWidth( $bits(core_backup_t) )
        ) i_tmr_core_checker_backup (
          .a_i        ( core_backup_i [tmr_core_id(i, 0)] ),
          .b_i        ( core_backup_i [tmr_core_id(i, 1)] ),
          .c_i        ( core_backup_i [tmr_core_id(i, 2)] ),
          .majority_o ( tmr_backup_outputs [       i    ] ),
          .error_o    ( tmr_failure_rr     [       i    ] ),
          .error_cba_o( tmr_error_rr       [       i    ] )
        );
        assign tmr_failure_o[i] = (tmr_core_en_o[tmr_core_id(i, 0)] &&
                                   rr_ctrl[tmr_shared_id(i)].rr_enable) ?
                                  tmr_failure_hmr[i] | tmr_failure_rr[i] :
                                  tmr_failure_hmr[i];
        for (genvar j = 0; j < 3; j++) begin : gen_tmr_error
          assign tmr_error_o[tmr_core_id(i,j)] = (tmr_core_en_o[tmr_core_id(i, j)] &&
                                                  rr_ctrl[tmr_shared_id(i)].rr_enable) ?
                                            tmr_error_hmr[tmr_core_id(i,j)] | tmr_error_rr[i][j] :
                                            tmr_error_hmr[tmr_core_id(i,j)];
        end
      end
      for (genvar i = NumTMRCores; i < NumCores; i++) begin : gen_remaining_core_err
        assign tmr_error_o[i] = '0;
      end
    end else begin : gen_no_tmr_rr
      assign tmr_backup_outputs = '0;
      assign tmr_failure_rr = '0;
      assign tmr_error_rr = '0;
      assign tmr_failure_o = tmr_failure_hmr;
      assign tmr_error_o = tmr_error_hmr;
    end
    for (genvar i = 0; i < NumRRUnits; i++) begin : gen_rapid_recovery
      assign rapid_recovery_backup_en_inp[i] = tmr_core_en_o[tmr_core_id(i, 0)] ?
                        (i < NumTMRGroups ? rapid_recovery_backup_en_oup[i] : 1'b0) : // TMR mode
                        dmr_core_en_o[dmr_core_id(i, 0)] ?
                          (rapid_recovery_backup_en_oup[i] & ~dmr_failure_o[i] )    : // DMR mode
                          1'b1;                                                       // Disabled

      assign rr_status[i].rr_error = tmr_core_en_o[tmr_core_id(i, 0)] ? |tmr_error_rr[i] :
                                     dmr_core_en_o[dmr_core_id(i, 0)] ? dmr_failure_rr[i] :
                                     '0;

      rapid_recovery_unit #(
        .RfAddrWidth    ( RfAddrWidth     ),
        .DataWidth      ( SysDataWidth    ),
        .EccEnabled     ( EccEnabled      ),
        .regfile_write_t( regfile_write_t ),
        .regfile_raddr_t( regfile_raddr_t ),
        .regfile_rdata_t( regfile_rdata_t ),
        .csr_intf_t     ( csr_intf_t      ),
        .pc_intf_t      ( pc_intf_t       )
      ) i_rr_unit (
        .clk_i,
        .rst_ni,

        .core_in_independent_i   ( ~dmr_core_en_o[dmr_core_id(i, 0)] &
                                   ~tmr_core_en_o[tmr_core_id(i, 0)]           ),
        .regfile_write_i         ( rapid_recovery_backup_bus[i].regfile_backup ),
        .backup_csr_i            ( rapid_recovery_backup_bus[i].csr_backup     ),
        .recovery_csr_o          ( rapid_recovery_bus[i].csr_recovery          ),
        .backup_pc_i             ( rapid_recovery_backup_bus[i].pc_backup      ),
        .recovery_pc_o           ( rapid_recovery_bus[i].pc_recovery           ),
        .backup_enable_i         ( rapid_recovery_backup_en_inp[i]             ),
        .start_recovery_i        ( rr_ctrl[i].recovery_start                   ),
        .backup_enable_o         ( rapid_recovery_backup_en_oup[i]             ),
        .recovery_finished_o     ( rr_status[i].recovery_finished              ),
        .setback_o               ( rapid_recovery_setback[i]                   ),
        .instr_lock_o            ( rapid_recovery_bus[i].instr_lock            ),
        .enable_pc_recovery_o    ( rapid_recovery_bus[i].pc_recovery_en        ),
        .enable_rf_recovery_o    ( rapid_recovery_bus[i].rf_recovery_en        ),
        .regfile_recovery_wdata_o( rapid_recovery_bus[i].rf_recovery_wdata     ),
        .regfile_recovery_rdata_o( rapid_recovery_bus[i].rf_recovery_rdata     ),
        .debug_halt_i            ( rapid_recovery_nominal[i].debug_halted      ),
        .debug_req_o             ( rapid_recovery_bus[i].debug_req             ),
        .debug_resume_o          ( rapid_recovery_bus[i].debug_resume          )
      );
    end

    always_comb begin : proc_rr_connection
      rapid_recovery_nominal    = '0;
      rapid_recovery_backup_bus = '0;
      for (int i = 0; i < NumDMRGroups; i++) begin
        if ((DMRFixed || (DMRSupported && dmr_core_en_o[dmr_core_id(i, 0)])) &&
            rr_ctrl[dmr_shared_id(i)].rr_enable) begin
          rapid_recovery_nominal   [dmr_shared_id(i)] = sys_nominal_outputs_o[dmr_core_id(i,0)];
          rapid_recovery_backup_bus[dmr_shared_id(i)] = dmr_backup_outputs   [            i   ];
        end
      end
      for (int i = 0; i < NumTMRGroups; i++) begin
        if ((TMRFixed || (TMRSupported && tmr_core_id[tmr_core_id(i, 0)])) &&
            rr_ctrl[tmr_shared_id(i)].rr_enable) begin
          rapid_recovery_nominal   [tmr_shared_id(i)] = sys_nominal_outputs_o[tmr_core_id(i,0)];
          rapid_recovery_backup_bus[tmr_shared_id(i)] = tmr_backup_outputs   [            i   ];
        end
      end
    end

    if (DMRSupported && TMRSupported) begin : gen_full_HMR
      /*****************
       *** TMR & DMR ***
       *****************/
      for (genvar i = 0; i < NumCores; i++) begin : gen_core_inputs
        always_comb begin
          rapid_recovery_o[i] =
                dmr_core_en_o [i] ? rapid_recovery_bus[dmr_shared_id(dmr_group_id(i))] :
                (tmr_core_en_o[i] ? rapid_recovery_bus[tmr_shared_id(tmr_group_id(i))] : '0);
          core_setback_o  [i] = hmr_setback   [i] |
                (dmr_core_en_o[i] ? rapid_recovery_setback[dmr_shared_id(dmr_group_id(i))] :
                (tmr_core_en_o[i] ? rapid_recovery_setback[tmr_shared_id(tmr_group_id(i))] : '0));
        end
      end
    end else if (TMRSupported || TMRFixed) begin : gen_TMR_only
      /***********
       *** TMR ***
       ***********/
      for (genvar i = 0; i < NumCores; i++) begin : gen_core_inputs
        always_comb begin
          rapid_recovery_o[i] = tmr_core_en_o [i] ?
                                rapid_recovery_bus[tmr_shared_id(tmr_group_id(i))] : '0;
          core_setback_o  [i] = hmr_setback   [i] |
                                (tmr_core_en_o[i] ?
                                 rapid_recovery_setback [tmr_shared_id(tmr_group_id(i))] : '0);
        end
      end

    end else if (DMRSupported || DMRFixed) begin : gen_DMR_only
      /*****************
       *** DMR ***
       *****************/
      for (genvar i = 0; i < NumCores; i++) begin : gen_core_inputs
        always_comb begin
          rapid_recovery_o[i] = dmr_core_en_o [i] ?
                                rapid_recovery_bus[dmr_shared_id(dmr_group_id(i))] : '0;
          core_setback_o  [i] = hmr_setback   [i] |
                                (dmr_core_en_o[i] ?
                                 rapid_recovery_setback [dmr_shared_id(dmr_group_id(i))] : '0);
        end
      end
    end else begin : gen_no_redundancy
      assign rapid_recovery_o = '0;
      assign core_setback_o = hmr_setback;
    end
  end else begin : gen_no_rr
    assign dmr_failure_o  = dmr_failure_hmr;
    assign tmr_failure_o  = tmr_failure_hmr;
    assign tmr_error_o    = tmr_error_hmr;
    assign core_setback_o = hmr_setback;
    assign rapid_recovery_nominal    = '0;
    assign rapid_recovery_backup_bus = '0;
    assign rapid_recovery_start      = '0;
    assign dmr_recovery_finished     = '0;
    assign tmr_recovery_finished     = '0;
  end

endmodule
