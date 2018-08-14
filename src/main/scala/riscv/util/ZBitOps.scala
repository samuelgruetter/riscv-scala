package riscv.util

object ZBitOps {

  def bitSlice(x: Long, start: Long, eend: Long): Long =
    (x >> start) & (~ ((-1L) << (eend - start)))

  def testbit(x: Long, i: Long): Boolean =
    (x & (1L << i)) != 0

  def signExtend(l: Long, n: Long): Long =
    if (testbit(n, l-1)) { n - (1L << l) } else { n }

}
