import Rv64Verifier.Proofs.Rodata
import Rv64Verifier.Image

/-!
# Contracts of called functions

What a caller assumes of a callee, stated once here: a function proof takes the contracts of its
callees as hypotheses, and each contract is proved by its own function's proof.
-/

namespace Rv64Verifier.Contracts
open RiscvZkvm.Rv64 LeanVM.Parameters

/-! ## `<E as Mul>::mul` (`field.rs`), at `0x80008c48` -/

/-- The stack bytes below `sp` that `mul` may use, its callees' included. -/
@[rv_addr] def mulStack : Nat := 1024

/-- `a0` = where the product goes (the return slot), `a1` = `self`, `a2` = `rhs`: valid `E`s,
the result apart from both operands, all three apart from the stack. -/
structure MulArgs (s : MachineState) : Prop where
  out : ValidMemRange (s.getReg .x10) 3
  lhs : ValidMemRange (s.getReg .x11) 3
  rhs : ValidMemRange (s.getReg .x12) 3
  stack : StackOk s mulStack
  outLhs : Apart (s.getReg .x10) 24 (s.getReg .x11) 24
  outRhs : Apart (s.getReg .x10) 24 (s.getReg .x12) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s mulStack) mulStack
  lhsStack : Apart (s.getReg .x11) 24 (stackLo s mulStack) mulStack
  rhsStack : Apart (s.getReg .x12) 24 (stackLo s mulStack) mulStack

/-- The arguments, and `.rodata` in place apart from the stack: `clmul_low` loads its mask from
it. -/
structure MulPre (s : MachineState) : Prop extends MulArgs s where
  rodata : RodataOk s
  stackRodata : Apart (stackLo s mulStack) mulStack rodataBase rodataSize

/-- `*out = self * rhs`; memory changes only in `*out` and the stack. -/
structure MulPost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) = eAt s (s.getReg .x11) * eAt s (s.getReg .x12)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 →
    ¬ Within a (stackLo s mulStack) mulStack → t.getMem a = s.getMem a

abbrev MulSpec : Prop := FunSpec Image.code 0x80008c48 MulPre MulPost

end Rv64Verifier.Contracts
