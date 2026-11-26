/-
  Rv64mc.Spec.Layout.Gpow

  The contract of `verifier::layout::gpow(index: u64) -> E`: `index` in `a0`, `Model.gpowRust index`'s limbs in
  `a0`, `a1`. A tail call of `GEN.pow`, so its stack is `E::pow`'s.
-/

import Rv64mc.Core.Holds
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout.Gpow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = (Model.limbs (Model.gpowRust (regs .x10))).1 ∧ r' .x11 = (Model.limbs (Model.gpowRust (regs .x10))).2

/-- **The contract of `gpow`**, function `i` of `p` with `need` bytes of stack, `E::pow`'s. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Layout.Gpow
