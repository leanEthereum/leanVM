/-
  Rv64mc.Spec.Multilinear.PolyEval

  The contract of `verifier::multilinear::poly_eval(coefficients: &[E], point: E) -> E`: the slice passed as a
  pointer and a length (`a0`, `a1`), its elements' limbs in the heap (`EListAt`, `Live`), the point's limbs in `a2`,
  `a3`; the result's limbs in `a0`, `a1` are `Model.polyEvalRust`'s value.
-/

import Rv64mc.Core.Repr
import Rv64mc.Spec.Field.EMul
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.PolyEval

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (cs : List E) (pt : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (cs.map Model.limbs) ∧
    env.Live m (regs .x10) (Layouts.E.byteSize * cs.length) ∧
    regs .x12 = (Model.limbs pt).1 ∧ regs .x13 = (Model.limbs pt).2

def Post (cs : List E) (pt : E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = (Model.limbs (Model.polyEvalRust cs pt)).1 ∧ r' .x11 = (Model.limbs (Model.polyEvalRust cs pt)).2

/-- **The contract of `poly_eval`**, function `i` of `p` with `need` bytes of stack (its frame is 64 bytes; it calls
    `E::mul`), for every slice and point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ cs pt, Holds env p i need (Pre env cs pt) (Post cs pt)

end Rv64mc.Spec.Multilinear.PolyEval
