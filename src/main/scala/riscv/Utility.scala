package riscv

object Utility {
  /* Meaning of MachineInt: an integer big enough to hold an integer of a RISCV machine,
     no matter whether it's a 32-bit or 64-bit machine. */
  type MachineInt = Long

  def machineIntToShamt(x: MachineInt): Long = x
}
