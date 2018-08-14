package riscv

import riscv.util.ZBitOps._

object Main {
  def main(args: Array[String]): Unit = {
    println(bitSlice(168, 2, 18))
  }
}
