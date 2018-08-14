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
  print_inductive InstructionI64.
  print_inductive InstructionI.
  print_inductive InstructionCSR. 
  print_inductive InstructionA64.
  print_inductive InstructionA.
  print_inductive Instruction.

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

  (* TODO
  print_fun1 isValidA.
  print_fun1 isValidA64.
  print_fun1 isValidCSR.
  print_fun1 isValidI.
  print_fun1 isValidI64.
  print_fun1 isValidM.
   *)
  idtac "def isValidA ( arg0 : InstructionA ) : Boolean = true // TODO".
  idtac "def isValidA64 ( arg0 : InstructionA64 ) : Boolean = true // TODO".
  idtac "def isValidCSR ( arg0 : InstructionCSR ) : Boolean = true // TODO".
  idtac "def isValidI ( arg0 : InstructionI ) : Boolean = true // TODO".
  idtac "def isValidI64 ( arg0 : InstructionI64 ) : Boolean = true // TODO".
  idtac "def isValidM ( arg0 : InstructionM ) : Boolean = true // TODO".  
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
