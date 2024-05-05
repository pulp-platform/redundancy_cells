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
 * Recovery Control Status Registers
 * ECC-protected register that stores the CSRs values from the cores
 * 
 */

module recovery_full_csr
  import rapid_recovery_pkg::*;
#(
  parameter  int unsigned ECCEnabled        = 0,
  parameter  int unsigned NonProtectedWidth = 32,
  parameter  int unsigned ParityWidth       = $clog2(NonProtectedWidth)+2,
  parameter  int unsigned ProtectedWidth    = NonProtectedWidth + ParityWidth,
  parameter      type     mstatus_t         = logic,
  parameter      type     hstatus_t         = logic,
  parameter      type     xlen_t            = logic,
  parameter      type     satp_t            = logic,
  parameter      type     hgatp_t           = logic,
  parameter      type     priv_lvl_t        = logic,
  parameter      type     intstatus_rv_t    = logic,
  parameter      type     intthresh_rv_t    = logic,
  parameter      type     pmpcfg_t          = logic,
  parameter      type     csr_intf_t        = logic,
  parameter      type     csr_reg_t         = logic,
  localparam int unsigned DataWidth  = ( ECCEnabled ) ? ProtectedWidth
                                                      : NonProtectedWidth
) (
  input  logic clk_i ,
  input  logic rst_ni,
  input  logic read_enable_i,
  input  logic write_enable_i,
  input  csr_intf_t backup_csr_i,
  output csr_intf_t recovery_csr_o
);

// CSRs using StdWidth:
// DPC
// Scratch0/1
// MTVEC
// MRVT
// MEDELEG
// MIDLEG
// MIP
// MIE
// MCOUNTEREN
// MSCRATCH
// MEPC
// MCAUSE
// MTVAL
// MTINST
// MTVAL2
// STVEC
// SCOUNTEREN
// STVT
// SSCRATCH
// SEPC
// SCAUSE
// STVAL
// HEDELEG
// HIDELEG
// HCOUNTEREN
// HGEIE
// HTVAL
// HTINST
// VSTVEC
// VSSCRATCH
// VSEPC
// VSCAUSE
// VSTVAL
// DCACHE
// ICACHE
// FENCET_PAD
// FENCET_CEIL
// ACC_CONS
// localparam int unsigned MstatusWidth = $bits(mstatus_t); // Used also for vsstatus
// localparam int unsigned EccMstatusParity = $clog2(MstatusWidth) + 2;
// localparam int unsigned HstatusWidth = $bits(hstatus_t);
// localparam int unsigned EccHstatusWidth = $clog2(HstatusWidth) + 2;
// localparam int unsigned XlenWidth = $bits(xlen_t); // Used for most of the CSRs
// localparam int unsigned EccXlenWidth = $clog2(XlenWidth) + 2;
// localparam int unsigned SatpWidth = $bits(satp_t); // Used for SATP/VSATP
// localparam int unsigned EccSatpWidth = $clog2(SatpWidth) + 2;
// localparam int unsigned HgatpWidth = $bits(hgatp_t);
// localparam int unsigned EccHgatpWidth = $clog2(HgatpWidth) + 2;
// localparam int unsigned PivLvlWidth = $bits(priv_lvl_t);
// localparam int unsigned EccPrivLvlWidth = $clog2(PrivLvlWidth) + 2;
// localparam int unsigned IntStatusWidth = $bits(intstatus_t);
// localparam int unsigned EccIntStatusWidth = $clog2(IntStatusWidth) + 2;
// localparam int unsigned IntThreshWidth = $bits(intthresh_t); // Used for [M/S]INTTHRESH
// localparam int unsigned EccIntthreshWidth = $clog2(IntThreshWidth) + 2;
// localparam int unsigned CycleWidth = $bits(logic [63:0]);
// localparam int unsigned EccCycleWidth = $clog2(CycleWidth) + 2;
// localparam int unsigned InstRetWidth = $bits(logic [63:0]);
// localparam int unsigned EccInstRetWidth = $clog2(IstRetWidth) + 2;
// localparam int unsigned PmpConfigWidth = $bits(pmpcfg_t);
// localparam int unsigned EccPmpConfigWidth = $clog2(PmpConfigWidth) + 2;

// typedef struct packed {
//   logic [ProtectedWidth-1:0] csr_mstatus;
//   logic [ProtectedWidth-1:0] csr_mie;
//   logic [ProtectedWidth-1:0] csr_mtvec;
//   logic [ProtectedWidth-1:0] csr_mscratch;
//   logic [ProtectedWidth-1:0] csr_mip;
//   logic [ProtectedWidth-1:0] csr_mepc;
//   logic [ProtectedWidth-1:0] csr_mcause;
// } ecc_csr_intf_t;

// typedef struct packed {
//   logic [MstatusWidth+EccMstatusParity-1:0] csr_mstatus;
//   logic [HstatusWidth+EccHstatusParity-1:0] csr_hstatus;
//   logic [MstatusWidth+EccMstatusParity-1:0] csr_vsstatus;
//   riscv::xlen_t       csr_mstatus_extended;
//   riscv::xlen_t       csr_vsstatus_extended;
//   riscv::satp_t       csr_vsatp;
//   riscv::satp_t       csr_satp;
//   riscv::hgatp_t      csr_hgatp;
//   riscv::dcsr_t       csr_dcsr;
//   riscv::csr_t        csr_csr_addr;
//   riscv::csr_t        csr_conv_csr_addr;
//   riscv::priv_lvl_t   csr_priv_lvl;
//   riscv::xlen_t csr_dpc;
//   riscv::xlen_t csr_dscratch0;
//   riscv::xlen_t csr_dscratch1;
//   riscv::xlen_t csr_mtvec;
//   riscv::xlen_t csr_mtvt;
//   riscv::xlen_t csr_medeleg;
//   riscv::xlen_t csr_mideleg;
//   riscv::xlen_t csr_mip;
//   riscv::xlen_t csr_mie;
//   riscv::intstatus_rv_t csr_mintstatus;
//   riscv::intthresh_rv_t csr_mintthresh;
//   riscv::xlen_t csr_mcounteren;
//   riscv::xlen_t csr_mscratch;
//   riscv::xlen_t csr_mepc;
//   riscv::xlen_t csr_mcause;
//   riscv::xlen_t csr_mtval;
//   riscv::xlen_t csr_mtinst;
//   riscv::xlen_t csr_mtval2;
//   logic csr_fiom;
//   riscv::xlen_t csr_stvec;
//   riscv::intthresh_rv_t csr_sintthresh;
//   riscv::xlen_t csr_scounteren;
//   riscv::xlen_t csr_stvt;
//   riscv::xlen_t csr_sscratch;
//   riscv::xlen_t csr_sepc;
//   riscv::xlen_t csr_scause;
//   riscv::xlen_t csr_stval;
//   riscv::xlen_t csr_hedeleg;
//   riscv::xlen_t csr_hideleg;
//   riscv::xlen_t csr_hcounteren;
//   riscv::xlen_t csr_hgeie;
//   riscv::xlen_t csr_htval;
//   riscv::xlen_t csr_htinst;
//   riscv::xlen_t csr_vstvec;
//   riscv::xlen_t csr_vsscratch;
//   riscv::xlen_t csr_vsepc;
//   riscv::xlen_t csr_vscause;
//   riscv::xlen_t csr_vstval;
//   riscv::xlen_t csr_dcache;
//   riscv::xlen_t csr_icache;
//   riscv::xlen_t csr_fence_t_pad;
//   riscv::xlen_t csr_fence_t_ceil;
//   riscv::xlen_t csr_acc_cons;
//   logic csr_wfi_d;
//   logic [63:0] csr_cycle;
//   logic [63:0] csr_instret;
//   riscv::pmpcfg_t [15:0] csr_pmpcfg_q;
//   logic [15:0][riscv::PLEN-3:0] csr_pmpaddr_q;
//   logic [MHPMCounterNum+3-1:0] csr_mcountinhibit;
// } ecc_csr_intf_t;

csr_intf_t csr_inp, csr_out;

logic [NonProtectedWidth-1:0] csr_dec_mstatus,
                              csr_dec_mie,
                              csr_dec_mtvec,
                              csr_dec_mscratch,
                              csr_dec_mip,
                              csr_dec_mepc,
                              csr_dec_mcause;

assign csr_inp = backup_csr_i;
assign recovery_csr_o = (read_enable_i) ? csr_out : '0;

if (ECCEnabled) begin : gen_ecc_csrs

  ecc_csr_intf_t csr_d, csr_q;

  // prim_secded_39_32_enc csr_mstatus_ecc_encoder (
  //   .in  ( {25'd0,csr_inp.csr_mstatus} ), // mtvec is a 7-bit value
  //   .out ( csr_d.csr_mstatus           )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mstatus_encoder (
    .in  ( {'d0,csr_inp.csr_mstatus} ),
    .out ( csr_d.csr_mstatus )
  );
  // prim_secded_39_32_enc csr_mie_ecc_encoder (
  //   .in  ( csr_inp.csr_mie ),
  //   .out ( csr_d.csr_mie   )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mie_encoder (
    .in  ( {'d0,csr_inp.csr_mie} ),
    .out ( csr_d.csr_mie )
  );
  // prim_secded_39_32_enc csr_mtvec_ecc_encoder (
  //   .in  ( {8'd0, csr_inp.csr_mtvec} ), // mtvec is a 24-bit value
  //   .out ( csr_d.csr_mtvec            )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mtvec_encoder (
    .in  ( {'d0,csr_inp.csr_mtvec} ),
    .out ( csr_d.csr_mtvec )
  );
  // prim_secded_39_32_enc csr_mscratch_ecc_encoder (
  //   .in  ( csr_inp.csr_mscratch ),
  //   .out ( csr_d.csr_mscratch   )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mscratch_encoder (
    .in  ( {'d0,csr_inp.csr_mscratch} ),
    .out ( csr_d.csr_mscratch )
  );
  // prim_secded_39_32_enc csr_mip_ecc_encoder (
  //   .in  ( csr_inp.csr_mip ),
  //   .out ( csr_d.csr_mip   )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mip_encoder (
    .in  ( {'d0,csr_inp.csr_mip} ),
    .out ( csr_d.csr_mip )
  );
  // prim_secded_39_32_enc csr_mepc_ecc_encoder (
  //   .in  ( csr_inp.csr_mepc),
  //   .out ( csr_d.csr_mepc  )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mepc_encoder (
    .in  ( {'d0,csr_inp.csr_mepc} ),
    .out ( csr_d.csr_mepc )
  );
  // prim_secded_39_32_enc csr_mcause_ecc_encoder (
  //   .in  ( {26'd0, csr_inp.csr_mcause} ), // mcause is a 6-bit value
  //   .out ( csr_d.csr_mcause            )
  // );
  hsiao_ecc_enc #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mcause_encoder (
    .in  ( {'d0,csr_inp.csr_mcause} ),
    .out ( csr_d.csr_mcause )
  );

  always_ff @(posedge clk_i, negedge rst_ni) begin : ecc_csr_backup
    if (~rst_ni)
      csr_q <= '0;
    else if (write_enable_i)
      csr_q <= csr_d;
  end

  // prim_secded_39_32_dec csr_mstatus_ecc_decoder (
  //   .in         ( csr_q.csr_mstatus ),
  //   .d_o        ( csr_dec_mstatus   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mstatus_decoder (
    .in         ( csr_q.csr_mstatus ),
    .out        ( csr_dec_mstatus   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  // prim_secded_39_32_dec csr_mie_ecc_decoder (
  //   .in         ( csr_q.csr_mie ),
  //   .d_o        ( csr_dec_mie   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mie_decoder (
    .in         ( csr_q.csr_mie ),
    .out        ( csr_dec_mie   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  // prim_secded_39_32_dec csr_mtvec_ecc_decoder (
  //   .in         ( csr_q.csr_mtvec ),
  //   .d_o        ( csr_dec_mtvec   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mtvec_decoder (
    .in         ( csr_q.csr_mtvec ),
    .out        ( csr_dec_mtvec   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  // prim_secded_39_32_dec csr_mscratch_ecc_decoder (
  //   .in         ( csr_q.csr_mscratch ),
  //   .d_o        ( csr_dec_mscratch   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mscratch_decoder (
    .in         ( csr_q.csr_mscratch ),
    .out        ( csr_dec_mscratch   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  // prim_secded_39_32_dec csr_mip_ecc_decoder (
  //   .in         ( csr_q.csr_mip ),
  //   .d_o        ( csr_dec_mip   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mip_decoder (
    .in         ( csr_q.csr_mip ),
    .out        ( csr_dec_mip   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  // prim_secded_39_32_dec csr_mepc_ecc_decoder (
  //   .in         ( csr_q.csr_mepc ),
  //   .d_o        ( csr_dec_mepc   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mepc_decoder (
    .in         ( csr_q.csr_mepc ),
    .out        ( csr_dec_mepc   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  // prim_secded_39_32_dec csr_mcause_ecc_decoder (
  //   .in         ( csr_q.csr_mcause ),
  //   .d_o        ( csr_dec_mcause   ),
  //   .syndrome_o ( ),
  //   .err_o      ( )
  // );
  hsiao_ecc_dec #(
    .DataWidth ( NonProtectedWidth ),
    .ProtWidth ( ParityWidth )
  ) i_mcause_decoder (
    .in         ( csr_q.csr_mcause ),
    .out        ( csr_dec_mcause   ),
    .syndrome_o ( ),
    .err_o      ( )
  );
  assign csr_out.csr_mstatus = csr_dec_mstatus[6:0];
  assign csr_out.csr_mie = csr_dec_mie;
  assign csr_out.csr_mtvec = csr_dec_mtvec[23:0];
  assign csr_out.csr_mscratch = csr_dec_mscratch;
  assign csr_out.csr_mip = csr_dec_mip;
  assign csr_out.csr_mepc = csr_dec_mepc;
  assign csr_out.csr_mcause = csr_dec_mcause[5:0];
end else begin : gen_no_ecc_csrs
  csr_intf_t csr_d, csr_q;

  assign csr_d = csr_inp;

  always_ff @(posedge clk_i, negedge rst_ni) begin : csr_backup
    if (~rst_ni)
      csr_q <= '0;
    else if (write_enable_i)
      csr_q <= csr_d;
  end
  assign csr_out = csr_q;

end

endmodule : recovery_full_csr
