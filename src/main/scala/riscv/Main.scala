package riscv

import riscv.util.ZBitOps._
import riscv.Decode._

object Main {

  val fib6: List[Long] = List(
    0x00600993,         // li s3,6
    0x00000a13,         // li s4,0
    0x00100913,         // li s2,1
    0x00000493,         // li s1,0
    0x0140006f,         // j 101e0 <main+0x44>
    0x012a0ab3,         // add s5,s4,s2
    0x00090a13,         // mv s4,s2
    0x000a8913,         // mv s2,s5
    0x00148493,         // addi s1,s1,1
    0xff34c8e3          // blt s1,s3,101d0 <main+0x34>
  )

  def decodeList(l: List[Long]): List[Instruction] = l.map(x => decode(RV32IM, x))

  def main(args: Array[String]): Unit = {
    println(decodeList(fib6))
  }
}
