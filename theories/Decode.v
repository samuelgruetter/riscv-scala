Require Import Coq.ZArith.ZArith.
Require Import riscv.util.ZBitOps.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscvscala.Tools.


Goal False.

  idtac "package riscv".
  idtac "import riscv.util.ZBitOps._".
  idtac "import riscv.Utility._".
  idtac "object Decode {".
  idtac "type Register = Long".
  idtac "type Opcode = Long".
  
  print_inductive InstructionSet.
  
  Notation "x 'match' { 'case' 'RV32I' => e1 ; 'case' 'RV32IM' => e2 ; 'case' 'RV32IA' => e3 ; 'case' 'RV32IMA' => e4 ; 'case' 'RV64I' => e5 ; 'case' 'RV64IM' => e6 ; 'case' 'RV64IA' => e7 ; 'case' 'RV64IMA' => e8 }" :=
  (match x with
    | RV32I => e1
    | RV32IM => e2
    | RV32IA => e3
    | RV32IMA => e4
    | RV64I => e5
    | RV64IM => e6
    | RV64IA => e7
    | RV64IMA => e8
   end) (at level 8).

  print_inductive InstructionM64.
   
  Notation "x 'match' { 'case' 'Mulw'  ( r00 , r01 , r02 ) => e1 ; 'case' 'Divw'  ( r10 , r11 , r12 ) => e2 ; 'case' 'Divuw' ( r20 , r21 , r22 ) => e3 ; 'case' 'Remw'  ( r30 , r31 , r32 ) => e4 ; 'case' 'Remuw' ( r40 , r41 , r42 ) => e5 ; 'case' 'InvalidM64' => e6 }" :=
    (match x with
     | Mulw  r00 r01 r02 => e1
     | Divw  r10 r11 r12 => e2
     | Divuw r20 r21 r22 => e3
     | Remw  r30 r31 r32 => e4
     | Remuw r40 r41 r42 => e5
     | InvalidM64     => e6
     end) (at level 8). 

  print_inductive InstructionM.

  Notation "x 'match' { 'case' 'Mul' ( ar , ar0 , ar1 ) => ea ; 'case' 'Mulh' ( br , br0 , br1 ) => eb ; 'case' 'Mulhsu' ( cr , cr0 , cr1 ) => ec ; 'case' 'Mulhu' ( dr , dr0 , dr1 ) => ed ; 'case' 'Div' ( er , er0 , er1 ) => ee ; 'case' 'Divu' ( fr , fr0 , fr1 ) => ef ; 'case' 'Rem' ( gr , gr0 , gr1 ) => eg ; 'case' 'Remu' ( hr , hr0 , hr1 ) => eh ; 'case' 'InvalidM' => ei }" :=
    (match x with
     | Mul ar ar0 ar1 => ea
     | Mulh br br0 br1 => eb
     | Mulhsu cr cr0 cr1 => ec
     | Mulhu dr dr0 dr1 => ed
     | Div er er0 er1 => ee
     | Divu fr fr0 fr1 => ef
     | Rem gr gr0 gr1 => eg
     | Remu hr hr0 hr1 => eh
     | InvalidM  => ei
     end) (at level 8).

  print_inductive InstructionI64.

  Notation "x 'match' { 'case' 'Ld' ( ar , ar0 , az ) => ae ; 'case' 'Lwu' ( br , br0 , bz ) => be ; 'case' 'Addiw' ( cr , cr0 , cz ) => ce ; 'case' 'Slliw' ( dr , dr0 , dz ) => de ; 'case' 'Srliw' ( er , er0 , ez ) => ee ; 'case' 'Sraiw' ( fr , fr0 , fz ) => fe ; 'case' 'Sd' ( gr , gr0 , gz ) => ge ; 'case' 'Addw' ( hr , hr0 , hr1 ) => he ; 'case' 'Subw' ( ir , ir0 , ir1 ) => ie ; 'case' 'Sllw' ( jr , jr0 , jr1 ) => je ; 'case' 'Srlw' ( kr , kr0 , kr1 ) => ke ; 'case' 'Sraw' ( lr , lr0 , lr1 ) => le ; 'case' 'InvalidI64' => me ; }" :=
    (match x with
     | Ld ar ar0 az => ae
     | Lwu br br0 bz => be
     | Addiw cr cr0 cz => ce
     | Slliw dr dr0 dz => de
     | Srliw er er0 ez => ee
     | Sraiw fr fr0 fz => fe
     | Sd gr gr0 gz => ge
     | Addw hr hr0 hr1 => he
     | Subw ir ir0 ir1 => ie
     | Sllw jr jr0 jr1 => je
     | Srlw kr kr0 kr1 => ke
     | Sraw lr lr0 lr1 => le
     | InvalidI64  => me
     end) (at level 8).

  print_inductive InstructionI.
  
  Notation "x 'match' { 'case' 'Lb'      ( ar , ar0 , az  ) => ae ; 'case' 'Lh'      ( br , br0 , bz  ) => be ; 'case' 'Lw'      ( cr , cr0 , cz  ) => ce ; 'case' 'Lbu'     ( dr , dr0 , dz  ) => de ; 'case' 'Lhu'     ( er , er0 , ez  ) => ee ; 'case' 'Fence'   ( fz , fz0       ) => fe ; 'case' 'Fence_i'                    => ge ; 'case' 'Addi'    ( hr , hr0 , hz  ) => he ; 'case' 'Slli'    ( ir , ir0 , iz  ) => ie ; 'case' 'Slti'    ( jr , jr0 , jz  ) => je ; 'case' 'Sltiu'   ( kr , kr0 , kz  ) => ke ; 'case' 'Xori'    ( lr , lr0 , lz  ) => le ; 'case' 'Ori'     ( mr , mr0 , mz  ) => me ; 'case' 'Andi'    ( nr , nr0 , nz  ) => ne ; 'case' 'Srli'    ( or , or0 , oz  ) => oe ; 'case' 'Srai'    ( pr , pr0 , pz  ) => pe ; 'case' 'Auipc'   ( qr , qz        ) => qe ; 'case' 'Sb'      ( rr , rr0 , rz  ) => re ; 'case' 'Sh'      ( sr , sr0 , sz  ) => se ; 'case' 'Sw'      ( tr , tr0 , tz  ) => te ; 'case' 'Add'     ( ur , ur0 , ur1 ) => ue ; 'case' 'Sub'     ( vr , vr0 , vr1 ) => ve ; 'case' 'Sll'     ( wr , wr0 , wr1 ) => we ; 'case' 'Slt'     ( xr , xr0 , xr1 ) => xe ; 'case' 'Sltu'    ( yr , yr0 , yr1 ) => ye ; 'case' 'Xor'     ( zr , zr0 , zr1 ) => ze ; 'case' 'Srl'     ( Ar , Ar0 , Ar1 ) => Ae ; 'case' 'Sra'     ( Br , Br0 , Br1 ) => Be ; 'case' 'Or'      ( Cr , Cr0 , Cr1 ) => Ce ; 'case' 'And'     ( Dr , Dr0 , Dr1 ) => De ; 'case' 'Lui'     ( Er , Ez        ) => Ee ; 'case' 'Beq'     ( Fr , Fr0 , Fz  ) => Fe ; 'case' 'Bne'     ( Gr , Gr0 , Gz  ) => Ge ; 'case' 'Blt'     ( Hr , Hr0 , Hz  ) => He ; 'case' 'Bge'     ( Ir , Ir0 , Iz  ) => Ie ; 'case' 'Bltu'    ( Jr , Jr0 , Jz  ) => Je ; 'case' 'Bgeu'    ( Kr , Kr0 , Kz  ) => Ke ; 'case' 'Jalr'    ( Lr , Lr0 , Lz  ) => Le ; 'case' 'Jal'     ( Mr , Mz        ) => Me ; 'case' 'InvalidI'                   => Ne }" :=
    (match x with
     | Lb      ar ar0 az  => ae
     | Lh      br br0 bz  => be
     | Lw      cr cr0 cz  => ce
     | Lbu     dr dr0 dz  => de
     | Lhu     er er0 ez  => ee
     | Fence   fz fz0     => fe
     | Fence_i            => ge
     | Addi    hr hr0 hz  => he
     | Slli    ir ir0 iz  => ie
     | Slti    jr jr0 jz  => je
     | Sltiu   kr kr0 kz  => ke
     | Xori    lr lr0 lz  => le
     | Ori     mr mr0 mz  => me
     | Andi    nr nr0 nz  => ne
     | Srli    or or0 oz  => oe
     | Srai    pr pr0 pz  => pe
     | Auipc   qr qz      => qe
     | Sb      rr rr0 rz  => re
     | Sh      sr sr0 sz  => se
     | Sw      tr tr0 tz  => te
     | Add     ur ur0 ur1 => ue
     | Sub     vr vr0 vr1 => ve
     | Sll     wr wr0 wr1 => we
     | Slt     xr xr0 xr1 => xe
     | Sltu    yr yr0 yr1 => ye
     | Xor     zr zr0 zr1 => ze
     | Srl     Ar Ar0 Ar1 => Ae
     | Sra     Br Br0 Br1 => Be
     | Or      Cr Cr0 Cr1 => Ce
     | And     Dr Dr0 Dr1 => De
     | Lui     Er Ez      => Ee
     | Beq     Fr Fr0 Fz  => Fe
     | Bne     Gr Gr0 Gz  => Ge
     | Blt     Hr Hr0 Hz  => He
     | Bge     Ir Ir0 Iz  => Ie
     | Bltu    Jr Jr0 Jz  => Je
     | Bgeu    Kr Kr0 Kz  => Ke
     | Jalr    Lr Lr0 Lz  => Le
     | Jal     Mr Mz      => Me
     | InvalidI           => Ne
     end) (at level 8).

  print_inductive InstructionCSR. 

  Notation "x 'match' { 'case' 'Ecall'                         => ae ; 'case' 'Ebreak'                        => be ; 'case' 'Uret'                          => ce ; 'case' 'Sret'                          => de ; 'case' 'Mret'                          => ee ; 'case' 'Wfi'                           => fe ; 'case' 'Sfence_vma' ( gr , gr0       ) => ge ; 'case' 'Csrrw'      ( hr , hr0 , hz  ) => he ; 'case' 'Csrrs'      ( ir , ir0 , iz  ) => ie ; 'case' 'Csrrc'      ( jr , jr0 , jz  ) => je ; 'case' 'Csrrwi'     ( kr , kz  , kz0 ) => ke ; 'case' 'Csrrsi'     ( lr , lz  , lz0 ) => le ; 'case' 'Csrrci'     ( mr , mz  , mz0 ) => me ; 'case' 'InvalidCSR'                    => ne }" :=
    (match x with
     | Ecall                 => ae
     | Ebreak                => be
     | Uret                  => ce
     | Sret                  => de
     | Mret                  => ee
     | Wfi                   => fe
     | Sfence_vma gr gr0     => ge
     | Csrrw      hr hr0 hz  => he
     | Csrrs      ir ir0 iz  => ie
     | Csrrc      jr jr0 jz  => je
     | Csrrwi     kr kz  kz0 => ke
     | Csrrsi     lr lz  lz0 => le
     | Csrrci     mr mz  mz0 => me
     | InvalidCSR            => ne
     end) (at level 8). 

  print_inductive InstructionA64.

  Notation "x 'match' { 'case' 'Lr_w'      ( ar , ar0 , az       ) => ea ; 'case' 'Sc_w'      ( br , br0 , br1 , bz ) => eb ; 'case' 'Amoswap_w' ( cr , cr0 , cr1 , cz ) => ec ; 'case' 'Amoadd_w'  ( dr , dr0 , dr1 , dz ) => ed ; 'case' 'Amoand_w'  ( er , er0 , er1 , ez ) => ee ; 'case' 'Amoor_w'   ( fr , fr0 , fr1 , fz ) => ef ; 'case' 'Amoxor_w'  ( gr , gr0 , gr1 , gz ) => eg ; 'case' 'Amomax_w'  ( hr , hr0 , hr1 , hz ) => eh ; 'case' 'Amomaxu_w' ( ir , ir0 , ir1 , iz ) => ei ; 'case' 'Amomin_w'  ( jr , jr0 , jr1 , jz ) => ej ; 'case' 'Amominu_w' ( kr , kr0 , kr1 , kz ) => ek  'case' 'InvalidA' => el }" :=
    (match x with
     | Lr_w      ar ar0 az     => ea
     | Sc_w      br br0 br1 bz => eb
     | Amoswap_w cr cr0 cr1 cz => ec
     | Amoadd_w  dr dr0 dr1 dz => ed
     | Amoand_w  er er0 er1 ez => ee
     | Amoor_w   fr fr0 fr1 fz => ef
     | Amoxor_w  gr gr0 gr1 gz => eg
     | Amomax_w  hr hr0 hr1 hz => eh
     | Amomaxu_w ir ir0 ir1 iz => ei
     | Amomin_w  jr jr0 jr1 jz => ej
     | Amominu_w kr kr0 kr1 kz => ek
     | InvalidA                => el
     end) (at level 8).
  
  print_inductive InstructionA.

  Notation "x 'match' { 'case' 'Lr_d'      ( ar , ar0 , az       ) => ae ; 'case' 'Sc_d'      ( br , br0 , br1 , bz ) => be ; 'case' 'Amoswap_d' ( cr , cr0 , cr1 , cz ) => ce ; 'case' 'Amoadd_d'  ( dr , dr0 , dr1 , dz ) => de ; 'case' 'Amoand_d'  ( er , er0 , er1 , ez ) => ee ; 'case' 'Amoor_d'   ( fr , fr0 , fr1 , fz ) => fe ; 'case' 'Amoxor_d'  ( gr , gr0 , gr1 , gz ) => ge ; 'case' 'Amomax_d'  ( hr , hr0 , hr1 , hz ) => he ; 'case' 'Amomaxu_d' ( ir , ir0 , ir1 , iz ) => ie ; 'case' 'Amomin_d'  ( jr , jr0 , jr1 , jz ) => je ; 'case' 'Amominu_d' ( kr , kr0 , kr1 , kz ) => ke ; 'case' 'InvalidA64'                        => le }" :=
    (match x with
     | Lr_d      ar ar0 az     => ae
     | Sc_d      br br0 br1 bz => be
     | Amoswap_d cr cr0 cr1 cz => ce
     | Amoadd_d  dr dr0 dr1 dz => de
     | Amoand_d  er er0 er1 ez => ee
     | Amoor_d   fr fr0 fr1 fz => fe
     | Amoxor_d  gr gr0 gr1 gz => ge
     | Amomax_d  hr hr0 hr1 hz => he
     | Amomaxu_d ir ir0 ir1 iz => ie
     | Amomin_d  jr jr0 jr1 jz => je
     | Amominu_d kr kr0 kr1 kz => ke
     | InvalidA64              => le
     end) (at level 8).

  print_inductive Instruction.

  Notation "x 'match' { 'case' 'IInstruction'       ( ai ) => ae ; 'case' 'MInstruction'       ( bi ) => be ; 'case' 'AInstruction'       ( ci ) => ce ; 'case' 'I64Instruction'     ( di ) => de ; 'case' 'M64Instruction'     ( ei ) => ee ; 'case' 'A64Instruction'     ( fi ) => fe ; 'case' 'CSRInstruction'     ( gi ) => ge ; 'case' 'InvalidInstruction' ( hz ) => he }" :=
    (match x with
     | IInstruction       ai => ae
     | MInstruction       bi => be
     | AInstruction       ci => ce
     | I64Instruction     di => de
     | M64Instruction     ei => ee
     | A64Instruction     fi => fe
     | CSRInstruction     gi => ge
     | InvalidInstruction hz => he
     end) (at level 8).
  
  print_fun1 bitwidth.

  print_fun0 funct12_EBREAK.
  print_fun0 funct12_ECALL.
  print_fun0 funct12_MRET.
  print_fun0 funct12_SRET.
  print_fun0 funct12_URET.
  print_fun0 funct12_WFI.
  print_fun0 funct3_ADD.
  print_fun0 funct3_ADDI.
  print_fun0 funct3_ADDIW.
  print_fun0 funct3_ADDW.
  print_fun0 funct3_AMOD.
  print_fun0 funct3_AMOW.
  print_fun0 funct3_AND.
  print_fun0 funct3_ANDI.
  print_fun0 funct3_BEQ.
  print_fun0 funct3_BGE.
  print_fun0 funct3_BGEU.
  print_fun0 funct3_BLT.
  print_fun0 funct3_BLTU.
  print_fun0 funct3_BNE.
  print_fun0 funct3_CSRRC.
  print_fun0 funct3_CSRRCI.
  print_fun0 funct3_CSRRS.
  print_fun0 funct3_CSRRSI.
  print_fun0 funct3_CSRRW.
  print_fun0 funct3_CSRRWI.
  print_fun0 funct3_DIV.
  print_fun0 funct3_DIVU.
  print_fun0 funct3_DIVUW.
  print_fun0 funct3_DIVW.
  print_fun0 funct3_FENCE.
  print_fun0 funct3_FENCE_I.
  print_fun0 funct3_LB.
  print_fun0 funct3_LBU.
  print_fun0 funct3_LD.
  print_fun0 funct3_LH.
  print_fun0 funct3_LHU.
  print_fun0 funct3_LW.
  print_fun0 funct3_LWU.
  print_fun0 funct3_MUL.
  print_fun0 funct3_MULH.
  print_fun0 funct3_MULHSU.
  print_fun0 funct3_MULHU.
  print_fun0 funct3_MULW.
  print_fun0 funct3_OR.
  print_fun0 funct3_ORI.
  print_fun0 funct3_PRIV.
  print_fun0 funct3_REM.
  print_fun0 funct3_REMU.
  print_fun0 funct3_REMUW.
  print_fun0 funct3_REMW.
  print_fun0 funct3_SB.
  print_fun0 funct3_SD.
  print_fun0 funct3_SH.
  print_fun0 funct3_SLL.
  print_fun0 funct3_SLLI.
  print_fun0 funct3_SLLIW.
  print_fun0 funct3_SLLW.
  print_fun0 funct3_SLT.
  print_fun0 funct3_SLTI.
  print_fun0 funct3_SLTIU.
  print_fun0 funct3_SLTU.
  print_fun0 funct3_SRA.
  print_fun0 funct3_SRAI.
  print_fun0 funct3_SRAIW.
  print_fun0 funct3_SRAW.
  print_fun0 funct3_SRL.
  print_fun0 funct3_SRLI.
  print_fun0 funct3_SRLIW.
  print_fun0 funct3_SRLW.
  print_fun0 funct3_SUB.
  print_fun0 funct3_SUBW.
  print_fun0 funct3_SW.
  print_fun0 funct3_XOR.
  print_fun0 funct3_XORI.
  print_fun0 funct5_AMOADD.
  print_fun0 funct5_AMOAND.
  print_fun0 funct5_AMOMAX.
  print_fun0 funct5_AMOMAXU.
  print_fun0 funct5_AMOMIN.
  print_fun0 funct5_AMOMINU.
  print_fun0 funct5_AMOOR.
  print_fun0 funct5_AMOSWAP.
  print_fun0 funct5_AMOXOR.
  print_fun0 funct5_LR.
  print_fun0 funct5_SC.
  print_fun0 funct6_SLLI.
  print_fun0 funct6_SRAI.
  print_fun0 funct6_SRLI.
  print_fun0 funct7_ADD.
  print_fun0 funct7_ADDW.
  print_fun0 funct7_AND.
  print_fun0 funct7_DIV.
  print_fun0 funct7_DIVU.
  print_fun0 funct7_DIVUW.
  print_fun0 funct7_DIVW.
  print_fun0 funct7_MUL.
  print_fun0 funct7_MULH.
  print_fun0 funct7_MULHSU.
  print_fun0 funct7_MULHU.
  print_fun0 funct7_MULW.
  print_fun0 funct7_OR.
  print_fun0 funct7_REM.
  print_fun0 funct7_REMU.
  print_fun0 funct7_REMUW.
  print_fun0 funct7_REMW.
  print_fun0 funct7_SFENCE_VMA.
  print_fun0 funct7_SLL.
  print_fun0 funct7_SLLIW.
  print_fun0 funct7_SLLW.
  print_fun0 funct7_SLT.
  print_fun0 funct7_SLTU.
  print_fun0 funct7_SRA.
  print_fun0 funct7_SRAIW.
  print_fun0 funct7_SRAW.
  print_fun0 funct7_SRL.
  print_fun0 funct7_SRLIW.
  print_fun0 funct7_SRLW.
  print_fun0 funct7_SUB.
  print_fun0 funct7_SUBW.
  print_fun0 funct7_XOR.
  
  print_fun1 isValidA.
  print_fun1 isValidA64.
  print_fun1 isValidCSR.
  print_fun1 isValidI.
  print_fun1 isValidI64.
  print_fun1 isValidM.
  print_fun1 isValidM64.
  
  print_fun0 opcode_AMO.
  print_fun0 opcode_AUIPC.
  print_fun0 opcode_BRANCH.
  print_fun0 opcode_JAL.
  print_fun0 opcode_JALR.
  print_fun0 opcode_LOAD.
  print_fun0 opcode_LOAD_FP.
  print_fun0 opcode_LUI.
  print_fun0 opcode_MADD.
  print_fun0 opcode_MISC_MEM.
  print_fun0 opcode_MSUB.
  print_fun0 opcode_NMADD.
  print_fun0 opcode_NMSUB.
  print_fun0 opcode_OP.
  print_fun0 opcode_OP_32.
  print_fun0 opcode_OP_FP.
  print_fun0 opcode_OP_IMM.
  print_fun0 opcode_OP_IMM_32.
  print_fun0 opcode_STORE.
  print_fun0 opcode_STORE_FP.
  print_fun0 opcode_SYSTEM.

  print_fun1 supportsA.
  print_fun1 supportsM.

  print_fun2 decode.

  idtac "}".
Abort.
