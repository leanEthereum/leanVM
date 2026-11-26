/-
  Rv64mc.Spec.Multilinear.StackOffsets

  The contract of `verifier::multilinear::stack_offsets(sizes: &[usize]) -> (Vec<u64>, usize)`: the result at
  `sret` (`a0`), the sizes as a slice of words (`a1`, `a2`, `WordsAt`); the result is `Model.stackOffsetsRust`'s:
  the offsets' `Vec<u64>` header (`VecAt WordsAt`, in a fresh block or empty) and the `log2` after it. The tuple's
  layout is not among `Gen/Layouts.lean`'s: the header first, the `usize` at `logOffset`, as the code stores them.
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.StackOffsets

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The bytes of `(Vec<u64>, usize)`, and where the `usize` sits. -/
abbrev byteSize : Nat := 32
abbrev logOffset : Nat := 24

def Pre (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) byteSize ∧ SliceArgs WordsAt m (regs .x11) (regs .x12) ws ∧
    env.Live m (regs .x11) (8 * ws.length)

def Post (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  (∃ ptr cap, VecAt WordsAt m' (regs .x10) ptr cap (Model.stackOffsetsRust (ws.map BitVec.toNat)).1 ∧
    (cap = 0 ∨ env.Fresh m m' ptr (8 * cap))) ∧
  m'.getMem (regs .x10 + BitVec.ofNat 64 logOffset) = BitVec.ofNat 64 (Model.stackOffsetsRust (ws.map BitVec.toNat)).2

/-- **The contract of `stack_offsets`**, function `i` of `p` with `need` bytes of stack (its frame is 64 bytes; it
    calls `try_allocate_in`, `handle_error` and `panic_bounds_check`), for every list of sizes. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post env ws) (Whir.SretOut byteSize)

end Rv64mc.Spec.Multilinear.StackOffsets
