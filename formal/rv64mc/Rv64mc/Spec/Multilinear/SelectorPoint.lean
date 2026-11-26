/-
  Rv64mc.Spec.Multilinear.SelectorPoint

  The contract of `verifier::multilinear::selector_point(selector: u64, length: usize) -> Vec<E>`: the result's
  header at `sret` (`a0`), the selector in `a1`, the length in `a2`; the result is `Model.selectorPointRust`'s, in a
  fresh block (`FreshVecE`). A length whose buffer would not fit an `isize` does not return (`handle_error`).
-/

import Rv64mc.Spec.Multilinear.Basic
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.SelectorPoint

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The result's slot is the caller's. -/
def Pre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize

def Post (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  FreshVecE env m m' (regs .x10) (Model.selectorPointRust (regs .x11) (regs .x12).toNat)

/-- **The contract of `selector_point`**, function `i` of `p` with `need` bytes of stack (its frame is 64 bytes; it
    calls `try_allocate_in`, `Vec::reserve` and `handle_error`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (Pre env) (Post env) (Whir.SretOut Layouts.Vec.byteSize)

end Rv64mc.Spec.Multilinear.SelectorPoint
