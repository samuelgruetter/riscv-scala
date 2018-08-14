package riscv
import riscv.util.ZBitOps._
import riscv.Utility._
object Decode {
type Register = Long
type Opcode = Long
sealed trait InstructionSet
case object RV32I extends InstructionSet
case object RV32IM extends InstructionSet
case object RV32IA extends InstructionSet
case object RV32IMA extends InstructionSet
case object RV64I extends InstructionSet
case object RV64IM extends InstructionSet
case object RV64IA extends InstructionSet
case object RV64IMA extends InstructionSet
sealed trait InstructionM64
case class Mulw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM64
case class Divw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM64
case class Divuw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM64
case class Remw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM64
case class Remuw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM64
case object InvalidM64 extends InstructionM64
sealed trait InstructionM
case class Mul ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Mulh ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Mulhsu ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Mulhu ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Div ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Divu ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Rem ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case class Remu ( r : Register , r0 : Register , r1 : Register ) extends
InstructionM
case object InvalidM extends InstructionM
sealed trait InstructionI64
case class Ld ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Lwu ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Addiw ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Slliw ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Srliw ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Sraiw ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Sd ( r : Register , r0 : Register , z : Long ) extends
InstructionI64
case class Addw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI64
case class Subw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI64
case class Sllw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI64
case class Srlw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI64
case class Sraw ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI64
case object InvalidI64 extends InstructionI64
sealed trait InstructionI
case class Lb ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Lh ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Lw ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Lbu ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Lhu ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Fence ( z : Long , z0 : Long ) extends InstructionI
case object Fence_i extends InstructionI
case class Addi ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Slli ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Slti ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Sltiu ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Xori ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Ori ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Andi ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Srli ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Srai ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Auipc ( r : Register , z : Long ) extends InstructionI
case class Sb ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Sh ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Sw ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Add ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Sub ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Sll ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Slt ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Sltu ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Xor ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Srl ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Sra ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Or ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class And ( r : Register , r0 : Register , r1 : Register ) extends
InstructionI
case class Lui ( r : Register , z : Long ) extends InstructionI
case class Beq ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Bne ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Blt ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Bge ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Bltu ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Bgeu ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Jalr ( r : Register , r0 : Register , z : Long ) extends
InstructionI
case class Jal ( r : Register , z : Long ) extends InstructionI
case object InvalidI extends InstructionI
sealed trait InstructionCSR
case object Ecall extends InstructionCSR
case object Ebreak extends InstructionCSR
case object Uret extends InstructionCSR
case object Sret extends InstructionCSR
case object Mret extends InstructionCSR
case object Wfi extends InstructionCSR
case class Sfence_vma ( r : Register , r0 : Register ) extends InstructionCSR
case class Csrrw ( r : Register , r0 : Register , z : Long ) extends
InstructionCSR
case class Csrrs ( r : Register , r0 : Register , z : Long ) extends
InstructionCSR
case class Csrrc ( r : Register , r0 : Register , z : Long ) extends
InstructionCSR
case class Csrrwi ( r : Register , z : Long , z0 : Long ) extends
InstructionCSR
case class Csrrsi ( r : Register , z : Long , z0 : Long ) extends
InstructionCSR
case class Csrrci ( r : Register , z : Long , z0 : Long ) extends
InstructionCSR
case object InvalidCSR extends InstructionCSR
sealed trait InstructionA64
case class Lr_d ( r : Register , r0 : Register , z : Long ) extends
InstructionA64
case class Sc_d ( r : Register , r0 : Register , r1 : Register , z : Long )
extends InstructionA64
case class Amoswap_d ( r : Register , r0 : Register , r1 : Register , z :
Long ) extends InstructionA64
case class Amoadd_d ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA64
case class Amoand_d ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA64
case class Amoor_d ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA64
case class Amoxor_d ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA64
case class Amomax_d ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA64
case class Amomaxu_d ( r : Register , r0 : Register , r1 : Register , z :
Long ) extends InstructionA64
case class Amomin_d ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA64
case class Amominu_d ( r : Register , r0 : Register , r1 : Register , z :
Long ) extends InstructionA64
case object InvalidA64 extends InstructionA64
sealed trait InstructionA
case class Lr_w ( r : Register , r0 : Register , z : Long ) extends
InstructionA
case class Sc_w ( r : Register , r0 : Register , r1 : Register , z : Long )
extends InstructionA
case class Amoswap_w ( r : Register , r0 : Register , r1 : Register , z :
Long ) extends InstructionA
case class Amoadd_w ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA
case class Amoand_w ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA
case class Amoor_w ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA
case class Amoxor_w ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA
case class Amomax_w ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA
case class Amomaxu_w ( r : Register , r0 : Register , r1 : Register , z :
Long ) extends InstructionA
case class Amomin_w ( r : Register , r0 : Register , r1 : Register , z : Long
) extends InstructionA
case class Amominu_w ( r : Register , r0 : Register , r1 : Register , z :
Long ) extends InstructionA
case object InvalidA extends InstructionA
sealed trait Instruction
case class IInstruction ( i : InstructionI ) extends Instruction
case class MInstruction ( i : InstructionM ) extends Instruction
case class AInstruction ( i : InstructionA ) extends Instruction
case class I64Instruction ( i : InstructionI64 ) extends Instruction
case class M64Instruction ( i : InstructionM64 ) extends Instruction
case class A64Instruction ( i : InstructionA64 ) extends Instruction
case class CSRInstruction ( i : InstructionCSR ) extends Instruction
case class InvalidInstruction ( z : Long ) extends Instruction
def bitwidth ( arg0 : InstructionSet ) : Long = {
arg0 match { case RV32I => 32; case RV32IM => 32; case RV32IA => 32;
case RV32IMA => 32; case RV64I => 64; case RV64IM => 64; case RV64IA => 64;
case RV64IMA => 64} }
val funct12_EBREAK : Long = 1
val funct12_ECALL : Long = 0
val funct12_MRET : Long = 770
val funct12_SRET : Long = 258
val funct12_URET : Long = 2
val funct12_WFI : Long = 261
val funct3_ADD : Long = 0
val funct3_ADDI : Long = 0
val funct3_ADDIW : Long = 0
val funct3_ADDW : Long = 0
val funct3_AMOD : Long = 3
val funct3_AMOW : Long = 2
val funct3_AND : Long = 7
val funct3_ANDI : Long = 7
val funct3_BEQ : Long = 0
val funct3_BGE : Long = 5
val funct3_BGEU : Long = 7
val funct3_BLT : Long = 4
val funct3_BLTU : Long = 6
val funct3_BNE : Long = 1
val funct3_CSRRC : Long = 3
val funct3_CSRRCI : Long = 7
val funct3_CSRRS : Long = 2
val funct3_CSRRSI : Long = 6
val funct3_CSRRW : Long = 1
val funct3_CSRRWI : Long = 5
val funct3_DIV : Long = 4
val funct3_DIVU : Long = 5
val funct3_DIVUW : Long = 5
val funct3_DIVW : Long = 4
val funct3_FENCE : Long = 0
val funct3_FENCE_I : Long = 1
val funct3_LB : Long = 0
val funct3_LBU : Long = 4
val funct3_LD : Long = 3
val funct3_LH : Long = 1
val funct3_LHU : Long = 5
val funct3_LW : Long = 2
val funct3_LWU : Long = 6
val funct3_MUL : Long = 0
val funct3_MULH : Long = 1
val funct3_MULHSU : Long = 2
val funct3_MULHU : Long = 3
val funct3_MULW : Long = 0
val funct3_OR : Long = 6
val funct3_ORI : Long = 6
val funct3_PRIV : Long = 0
val funct3_REM : Long = 6
val funct3_REMU : Long = 7
val funct3_REMUW : Long = 7
val funct3_REMW : Long = 6
val funct3_SB : Long = 0
val funct3_SD : Long = 3
val funct3_SH : Long = 1
val funct3_SLL : Long = 1
val funct3_SLLI : Long = 1
val funct3_SLLIW : Long = 1
val funct3_SLLW : Long = 1
val funct3_SLT : Long = 2
val funct3_SLTI : Long = 2
val funct3_SLTIU : Long = 3
val funct3_SLTU : Long = 3
val funct3_SRA : Long = 5
val funct3_SRAI : Long = 5
val funct3_SRAIW : Long = 5
val funct3_SRAW : Long = 5
val funct3_SRL : Long = 5
val funct3_SRLI : Long = 5
val funct3_SRLIW : Long = 5
val funct3_SRLW : Long = 5
val funct3_SUB : Long = 0
val funct3_SUBW : Long = 0
val funct3_SW : Long = 2
val funct3_XOR : Long = 4
val funct3_XORI : Long = 4
val funct5_AMOADD : Long = 0
val funct5_AMOAND : Long = 12
val funct5_AMOMAX : Long = 20
val funct5_AMOMAXU : Long = 28
val funct5_AMOMIN : Long = 16
val funct5_AMOMINU : Long = 24
val funct5_AMOOR : Long = 8
val funct5_AMOSWAP : Long = 1
val funct5_AMOXOR : Long = 4
val funct5_LR : Long = 2
val funct5_SC : Long = 3
val funct6_SLLI : Long = 0
val funct6_SRAI : Long = 16
val funct6_SRLI : Long = 0
val funct7_ADD : Long = 0
val funct7_ADDW : Long = 0
val funct7_AND : Long = 0
val funct7_DIV : Long = 1
val funct7_DIVU : Long = 1
val funct7_DIVUW : Long = 1
val funct7_DIVW : Long = 1
val funct7_MUL : Long = 1
val funct7_MULH : Long = 1
val funct7_MULHSU : Long = 1
val funct7_MULHU : Long = 1
val funct7_MULW : Long = 1
val funct7_OR : Long = 0
val funct7_REM : Long = 1
val funct7_REMU : Long = 1
val funct7_REMUW : Long = 1
val funct7_REMW : Long = 1
val funct7_SFENCE_VMA : Long = 9
val funct7_SLL : Long = 0
val funct7_SLLIW : Long = 0
val funct7_SLLW : Long = 0
val funct7_SLT : Long = 0
val funct7_SLTU : Long = 0
val funct7_SRA : Long = 32
val funct7_SRAIW : Long = 32
val funct7_SRAW : Long = 32
val funct7_SRL : Long = 0
val funct7_SRLIW : Long = 0
val funct7_SRLW : Long = 0
val funct7_SUB : Long = 32
val funct7_SUBW : Long = 32
val funct7_XOR : Long = 0
def isValidA ( arg0 : InstructionA ) : Boolean = true // TODO
def isValidA64 ( arg0 : InstructionA64 ) : Boolean = true // TODO
def isValidCSR ( arg0 : InstructionCSR ) : Boolean = true // TODO
def isValidI ( arg0 : InstructionI ) : Boolean = true // TODO
def isValidI64 ( arg0 : InstructionI64 ) : Boolean = true // TODO
def isValidM ( arg0 : InstructionM ) : Boolean = true // TODO
def isValidM64 ( arg0 : InstructionM64 ) : Boolean = {
arg0 match { case Mulw (_, _, _)=> true; case Divw (_, _, _)=> true;
case Divuw (_, _, _)=> true; case Remw (_, _, _)=> true; case Remuw (_, _, _)
=> true; case InvalidM64 => false} }
val opcode_AMO : Opcode = 47
val opcode_AUIPC : Opcode = 23
val opcode_BRANCH : Opcode = 99
val opcode_JAL : Opcode = 111
val opcode_JALR : Opcode = 103
val opcode_LOAD : Opcode = 3
val opcode_LOAD_FP : Opcode = 7
val opcode_LUI : Opcode = 55
val opcode_MADD : Opcode = 67
val opcode_MISC_MEM : Opcode = 15
val opcode_MSUB : Opcode = 71
val opcode_NMADD : Opcode = 79
val opcode_NMSUB : Opcode = 75
val opcode_OP : Opcode = 51
val opcode_OP_32 : Opcode = 59
val opcode_OP_FP : Opcode = 83
val opcode_OP_IMM : Opcode = 19
val opcode_OP_IMM_32 : Opcode = 27
val opcode_STORE : Opcode = 35
val opcode_STORE_FP : Opcode = 39
val opcode_SYSTEM : Opcode = 115
def supportsA ( arg0 : InstructionSet ) : Boolean = {
arg0 match { case RV32I => false; case RV32IM => false; case RV32IA => true;
case RV32IMA => true; case RV64I => false; case RV64IM => false;
case RV64IA => true; case RV64IMA => true} }
def supportsM ( arg0 : InstructionSet ) : Boolean = {
arg0 match { case RV32I => false; case RV32IM => true; case RV32IA => false;
case RV32IMA => true; case RV64I => false; case RV64IM => true;
case RV64IA => false; case RV64IMA => true} }
def decode ( arg0 : InstructionSet , arg1 : Long ) : Instruction = {
val aqrl = bitSlice(arg1, 25, 27);
val funct5 = bitSlice(arg1, 27, 32);
val zimm = bitSlice(arg1, 15, 20);
val funct6 = bitSlice(arg1, 26, 32);
val shamtHi = bitSlice(arg1, 25, 26);
val shamtHiTest = shamtHi == 0 || bitwidth(arg0) == 64;
val shamt6 = machineIntToShamt(bitSlice(arg1, 20, 26));
val shamt5 = machineIntToShamt(bitSlice(arg1, 20, 25));
val sbimm12 =
signExtend(13, (((bitSlice(arg1, 31, 32) << 12)
                 | (bitSlice(arg1, 25, 31) << 5))
                | (bitSlice(arg1, 8, 12) << 1))
               | (bitSlice(arg1, 7, 8) << 11));
val simm12 =
signExtend(12, (bitSlice(arg1, 25, 32) << 5) | bitSlice(arg1, 7, 12));
val csr12 = bitSlice(arg1, 20, 32);
val oimm12 = signExtend(12, bitSlice(arg1, 20, 32));
val imm12 = signExtend(12, bitSlice(arg1, 20, 32));
val jimm20 =
signExtend(21, (((bitSlice(arg1, 31, 32) << 20)
                 | (bitSlice(arg1, 21, 31) << 1))
                | (bitSlice(arg1, 20, 21) << 11))
               | (bitSlice(arg1, 12, 20) << 12));
val oimm20 = signExtend(32, bitSlice(arg1, 12, 32) << 12);
val imm20 = signExtend(32, bitSlice(arg1, 12, 32) << 12);
val msb4 = bitSlice(arg1, 28, 32);
val pred = bitSlice(arg1, 24, 28);
val succ = bitSlice(arg1, 20, 24);
val rs3 = bitSlice(arg1, 27, 32);
val rs2 = bitSlice(arg1, 20, 25);
val rs1 = bitSlice(arg1, 15, 20);
val rd = bitSlice(arg1, 7, 12);
val funct12 = bitSlice(arg1, 20, 32);
val funct10 = (bitSlice(arg1, 25, 32) << 3) | bitSlice(arg1, 12, 15);
val funct7 = bitSlice(arg1, 25, 32);
val funct3 = bitSlice(arg1, 12, 15);
val opcode = bitSlice(arg1, 0, 7);
val decodeI = if (opcode == opcode_LOAD && funct3 == funct3_LB) {
Lb(rd, rs1, oimm12) } else {
if (opcode == opcode_LOAD && funct3 == funct3_LH) { Lh(rd, rs1, oimm12)
 } else { if (opcode == opcode_LOAD && funct3 == funct3_LW) {
Lw(rd, rs1, oimm12) } else {
if (opcode == opcode_LOAD && funct3 == funct3_LBU) { Lbu(rd, rs1, oimm12)
 } else { if (opcode == opcode_LOAD && funct3 == funct3_LHU) {
Lhu(rd, rs1, oimm12) } else {
if (opcode == opcode_MISC_MEM &&
    (rd == 0 && (funct3 == funct3_FENCE && (rs1 == 0 && msb4 == 0)))) {
Fence(pred, succ) } else {
if (opcode == opcode_MISC_MEM &&
    (rd == 0 && (funct3 == funct3_FENCE_I && (rs1 == 0 && imm12 == 0)))) {
Fence_i } else { if (opcode == opcode_OP_IMM && funct3 == funct3_ADDI) {
Addi(rd, rs1, imm12) } else {
if (opcode == opcode_OP_IMM && funct3 == funct3_SLTI) { Slti(rd, rs1, imm12)
 } else { if (opcode == opcode_OP_IMM && funct3 == funct3_SLTIU) {
Sltiu(rd, rs1, imm12) } else {
if (opcode == opcode_OP_IMM && funct3 == funct3_XORI) { Xori(rd, rs1, imm12)
 } else { if (opcode == opcode_OP_IMM && funct3 == funct3_ORI) {
Ori(rd, rs1, imm12) } else {
if (opcode == opcode_OP_IMM && funct3 == funct3_ANDI) { Andi(rd, rs1, imm12)
 } else {
if (opcode == opcode_OP_IMM &&
    (funct3 == funct3_SLLI && (funct6 == funct6_SLLI && shamtHiTest))) {
Slli(rd, rs1, shamt6) } else {
if (opcode == opcode_OP_IMM &&
    (funct3 == funct3_SRLI && (funct6 == funct6_SRLI && shamtHiTest))) {
Srli(rd, rs1, shamt6) } else {
if (opcode == opcode_OP_IMM &&
    (funct3 == funct3_SRAI && (funct6 == funct6_SRAI && shamtHiTest))) {
Srai(rd, rs1, shamt6) } else { if (opcode == opcode_AUIPC) {
Auipc(rd, oimm20) } else {
if (opcode == opcode_STORE && funct3 == funct3_SB) { Sb(rs1, rs2, simm12)
 } else { if (opcode == opcode_STORE && funct3 == funct3_SH) {
Sh(rs1, rs2, simm12) } else {
if (opcode == opcode_STORE && funct3 == funct3_SW) { Sw(rs1, rs2, simm12)
 } else {
if (opcode == opcode_OP && (funct3 == funct3_ADD && funct7 == funct7_ADD)) {
Add(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_SUB && funct7 == funct7_SUB)) {
Sub(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_SLL && funct7 == funct7_SLL)) {
Sll(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_SLT && funct7 == funct7_SLT)) {
Slt(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_SLTU && funct7 == funct7_SLTU)) {
Sltu(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_XOR && funct7 == funct7_XOR)) {
Xor(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_SRL && funct7 == funct7_SRL)) {
Srl(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_SRA && funct7 == funct7_SRA)) {
Sra(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_OR && funct7 == funct7_OR)) {
Or(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_AND && funct7 == funct7_AND)) {
And(rd, rs1, rs2) } else { if (opcode == opcode_LUI) { Lui(rd, imm20)
 } else { if (opcode == opcode_BRANCH && funct3 == funct3_BEQ) {
Beq(rs1, rs2, sbimm12) } else {
if (opcode == opcode_BRANCH && funct3 == funct3_BNE) { Bne(rs1, rs2, sbimm12)
 } else { if (opcode == opcode_BRANCH && funct3 == funct3_BLT) {
Blt(rs1, rs2, sbimm12) } else {
if (opcode == opcode_BRANCH && funct3 == funct3_BGE) { Bge(rs1, rs2, sbimm12)
 } else { if (opcode == opcode_BRANCH && funct3 == funct3_BLTU) {
Bltu(rs1, rs2, sbimm12) } else {
if (opcode == opcode_BRANCH && funct3 == funct3_BGEU) {
Bgeu(rs1, rs2, sbimm12) } else { if (opcode == opcode_JALR) {
Jalr(rd, rs1, oimm12) } else { if (opcode == opcode_JAL) { Jal(rd, jimm20)
 } else { InvalidI } } } } } } } } } } } } } } } } } } } } } } } } } } } } }
 } } } } } } } } } };
val decodeM =
if (opcode == opcode_OP && (funct3 == funct3_MUL && funct7 == funct7_MUL)) {
Mul(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_MULH && funct7 == funct7_MULH)) {
Mulh(rd, rs1, rs2) } else {
if (opcode == opcode_OP &&
    (funct3 == funct3_MULHSU && funct7 == funct7_MULHSU)) {
Mulhsu(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_MULHU && funct7 == funct7_MULHU)) {
Mulhu(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_DIV && funct7 == funct7_DIV)) {
Div(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_DIVU && funct7 == funct7_DIVU)) {
Divu(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_REM && funct7 == funct7_REM)) {
Rem(rd, rs1, rs2) } else {
if (opcode == opcode_OP && (funct3 == funct3_REMU && funct7 == funct7_REMU)) {
Remu(rd, rs1, rs2) } else { InvalidM } } } } } } } };
val decodeA =
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && (funct5 == funct5_LR && rs2 == 0))) {
Lr_w(rd, rs1, aqrl) } else {
if (opcode == opcode_AMO && (funct3 == funct3_AMOW && funct5 == funct5_SC)) {
Sc_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOSWAP)) {
Amoswap_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOADD)) {
Amoadd_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOXOR)) {
Amoxor_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOAND)) {
Amoand_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO && (funct3 == funct3_AMOW && funct5 == funct5_AMOOR)) {
Amoor_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOMIN)) {
Amomin_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOMAX)) {
Amomax_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOMINU)) {
Amominu_w(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOW && funct5 == funct5_AMOMAXU)) {
Amomaxu_w(rd, rs1, rs2, aqrl) } else { InvalidA } } } } } } } } } } };
val decodeI64 = if (opcode == opcode_LOAD && funct3 == funct3_LD) {
Ld(rd, rs1, oimm12) } else {
if (opcode == opcode_LOAD && funct3 == funct3_LWU) { Lwu(rd, rs1, oimm12)
 } else { if (opcode == opcode_OP_IMM_32 && funct3 == funct3_ADDIW) {
Addiw(rd, rs1, imm12) } else {
if (opcode == opcode_OP_IMM_32 &&
    (funct3 == funct3_SLLIW && funct7 == funct7_SLLIW)) {
Slliw(rd, rs1, shamt5) } else {
if (opcode == opcode_OP_IMM_32 &&
    (funct3 == funct3_SRLIW && funct7 == funct7_SRLIW)) {
Srliw(rd, rs1, shamt5) } else {
if (opcode == opcode_OP_IMM_32 &&
    (funct3 == funct3_SRAIW && funct7 == funct7_SRAIW)) {
Sraiw(rd, rs1, shamt5) } else {
if (opcode == opcode_STORE && funct3 == funct3_SD) { Sd(rs1, rs2, simm12)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_ADDW && funct7 == funct7_ADDW)) { Addw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_SUBW && funct7 == funct7_SUBW)) { Subw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_SLLW && funct7 == funct7_SLLW)) { Sllw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_SRLW && funct7 == funct7_SRLW)) { Srlw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_SRAW && funct7 == funct7_SRAW)) { Sraw(rd, rs1, rs2)
 } else { InvalidI64 } } } } } } } } } } } };
val decodeM64 =
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_MULW && funct7 == funct7_MULW)) { Mulw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_DIVW && funct7 == funct7_DIVW)) { Divw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_DIVUW && funct7 == funct7_DIVUW)) { Divuw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_REMW && funct7 == funct7_REMW)) { Remw(rd, rs1, rs2)
 } else {
if (opcode == opcode_OP_32 &&
    (funct3 == funct3_REMUW && funct7 == funct7_REMUW)) { Remuw(rd, rs1, rs2)
 } else { InvalidM64 } } } } };
val decodeA64 =
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && (funct5 == funct5_LR && rs2 == 0))) {
Lr_d(rd, rs1, aqrl) } else {
if (opcode == opcode_AMO && (funct3 == funct3_AMOD && funct5 == funct5_SC)) {
Sc_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOSWAP)) {
Amoswap_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOADD)) {
Amoadd_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOXOR)) {
Amoxor_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOAND)) {
Amoand_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO && (funct3 == funct3_AMOD && funct5 == funct5_AMOOR)) {
Amoor_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOMIN)) {
Amomin_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOMAX)) {
Amomax_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOMINU)) {
Amominu_d(rd, rs1, rs2, aqrl) } else {
if (opcode == opcode_AMO &&
    (funct3 == funct3_AMOD && funct5 == funct5_AMOMAXU)) {
Amomaxu_d(rd, rs1, rs2, aqrl) } else { InvalidA64 } } } } } } } } } } };
val decodeCSR =
if (opcode == opcode_SYSTEM &&
    (rd == 0 && (funct3 == funct3_PRIV && funct7 == funct7_SFENCE_VMA))) {
Sfence_vma(rs1, rs2) } else {
if (opcode == opcode_SYSTEM &&
    (rd == 0 &&
     (funct3 == funct3_PRIV && (rs1 == 0 && funct12 == funct12_ECALL)))) {
Ecall } else {
if (opcode == opcode_SYSTEM &&
    (rd == 0 &&
     (funct3 == funct3_PRIV && (rs1 == 0 && funct12 == funct12_EBREAK)))) {
Ebreak } else {
if (opcode == opcode_SYSTEM &&
    (rd == 0 &&
     (funct3 == funct3_PRIV && (rs1 == 0 && funct12 == funct12_URET)))) {
Uret } else {
if (opcode == opcode_SYSTEM &&
    (rd == 0 &&
     (funct3 == funct3_PRIV && (rs1 == 0 && funct12 == funct12_SRET)))) {
Sret } else {
if (opcode == opcode_SYSTEM &&
    (rd == 0 &&
     (funct3 == funct3_PRIV && (rs1 == 0 && funct12 == funct12_MRET)))) {
Mret } else {
if (opcode == opcode_SYSTEM &&
    (rd == 0 &&
     (funct3 == funct3_PRIV && (rs1 == 0 && funct12 == funct12_WFI)))) { Wfi
 } else { if (opcode == opcode_SYSTEM && funct3 == funct3_CSRRW) {
Csrrw(rd, rs1, csr12) } else {
if (opcode == opcode_SYSTEM && funct3 == funct3_CSRRS) {
Csrrs(rd, rs1, csr12) } else {
if (opcode == opcode_SYSTEM && funct3 == funct3_CSRRC) {
Csrrc(rd, rs1, csr12) } else {
if (opcode == opcode_SYSTEM && funct3 == funct3_CSRRWI) {
Csrrwi(rd, zimm, csr12) } else {
if (opcode == opcode_SYSTEM && funct3 == funct3_CSRRSI) {
Csrrsi(rd, zimm, csr12) } else {
if (opcode == opcode_SYSTEM && funct3 == funct3_CSRRCI) {
Csrrci(rd, zimm, csr12) } else { InvalidCSR } } } } } } } } } } } } };
val resultCSR = if (isValidCSR(decodeCSR)) { CSRInstruction(decodeCSR) :: Nil
 } else { Nil };
val resultA64 = if (isValidA64(decodeA64)) { A64Instruction(decodeA64) :: Nil
 } else { Nil };
val resultM64 = if (isValidM64(decodeM64)) { M64Instruction(decodeM64) :: Nil
 } else { Nil };
val resultI64 = if (isValidI64(decodeI64)) { I64Instruction(decodeI64) :: Nil
 } else { Nil };
val resultA = if (isValidA(decodeA)) { AInstruction(decodeA) :: Nil } else {
Nil };
val resultM = if (isValidM(decodeM)) { MInstruction(decodeM) :: Nil } else {
Nil };
val resultI = if (isValidI(decodeI)) { IInstruction(decodeI) :: Nil } else {
Nil };
val results =
resultI ++
(if (supportsM(arg0)) { resultM } else { Nil }) ++
(if (supportsA(arg0)) { resultA } else { Nil }) ++
(if (bitwidth(arg0) == 64) { resultI64 } else { Nil }) ++
(if (bitwidth(arg0) == 64 && supportsM(arg0)) { resultM64 } else { Nil }) ++
(if (bitwidth(arg0) == 64 && supportsA(arg0)) { resultA64 } else { Nil }) ++
resultCSR;
results match { case Nil => InvalidInstruction(arg1); case singleResult
:: Nil => singleResult; case singleResult :: _ :: _ =>
InvalidInstruction(arg1)} }
}
