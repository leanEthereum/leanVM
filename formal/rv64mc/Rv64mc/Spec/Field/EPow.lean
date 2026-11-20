/-
  Rv64mc.Spec.Field.EPow

  The contract of `E::pow` as the image has it: every caller raises `GEN` (`layout::gpow`), so the compiler fixed
  `self` to `GEN` and passes only the exponent, in `a0`. The result's limbs are `Model.ePow Model.eGen`'s, in `a0`,
  `a1`; `Model.ePow_eq` makes it the power in `E`.
-/

import Rv64mc.Spec.Field.ESquare
import Rv64mc.Spec.Field.EMul

namespace Rv64mc.Spec.Field.EPow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = (Model.ePow Model.eGen (regs .x10)).1 ∧ r' .x11 = (Model.ePow Model.eGen (regs .x10)).2

/-- **The contract of `GEN.pow`**, function `i` of `p` with `need` bytes of stack (its frame is 48 bytes; it calls
    `E::square` and `E::mul`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.EPow
