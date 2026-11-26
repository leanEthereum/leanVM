/-
  Rv64mc.Spec.Multilinear.PaddingWeight

  The contract of `verifier::multilinear::padding_weight(point: &[E], n: u64) -> E`: the slice passed as a pointer
  and a length (`a0`, `a1`), its elements' limbs in the heap (`EListAt`, `Live`), `n` in `a2`; the result's limbs in
  `a0`, `a1` are `Model.paddingWeightRust`'s value.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.PaddingWeight

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (xs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (xs.map Model.limbs) ∧
    env.Live m (regs .x10) (Layouts.E.byteSize * xs.length)

def Post (xs : List E) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = (Model.limbs (Model.paddingWeightRust xs (regs .x12))).1 ∧
    r' .x11 = (Model.limbs (Model.paddingWeightRust xs (regs .x12))).2

/-- **The contract of `padding_weight`**, function `i` of `p` with `need` bytes of stack (its frame is 96 bytes; it
    calls `E::mul`, and tail-calls it), for every point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs, Holds env p i need (Pre env xs) (Post xs)

end Rv64mc.Spec.Multilinear.PaddingWeight
