/-
  Rv64mc.Spec.Multilinear.EqEval

  The contract of `verifier::multilinear::eq_eval(left: &[E], right: &[E]) -> E`: each slice passed as a pointer
  and a length (`a0`, `a1` and `a2`, `a3`), its elements' limbs in the heap (`EListAt`, `Live`); the result's limbs in
  `a0`, `a1` are `Model.eqEvalRust`'s value, wherever it has one (the lengths agree; otherwise `assert_eq!` does
  not return).
-/

import Rv64mc.Core.Repr
import Rv64mc.Spec.Field.EMul
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.EqEval

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The stack it needs: its frame (48 bytes) and `E::mul`'s. -/
def need : Nat := 48 + Field.EMul.need

def Pre (env : Env) (xs ys : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (xs.map Model.limbs) ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (ys.map Model.limbs) ∧
    env.Live m (regs .x10) (Layouts.E.byteSize * xs.length) ∧ env.Live m (regs .x12) (Layouts.E.byteSize * ys.length)

def Post (xs ys : List E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  ∀ v, Model.eqEvalRust xs ys = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `eq_eval`**, function `i` of `p`, for every pair of slices. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ xs ys, Holds env p i need (Pre env xs ys) (Post xs ys)

end Rv64mc.Spec.Multilinear.EqEval
