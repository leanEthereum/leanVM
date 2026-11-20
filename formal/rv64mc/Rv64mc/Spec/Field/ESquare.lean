/-
  Rv64mc.Spec.Field.ESquare

  The contract of `E::square`: `self` (limbs in `a0`, `a1`) squared, as `Model.eSquare` computes it on limbs, in
  `a0`, `a1`. `Model.eSquare_eq` makes it the square in `E`.
-/

import Rv64mc.Spec.Field.Spread
import Rv64mc.Spec.Field.Reduce

namespace Rv64mc.Spec.Field.ESquare

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = (Model.eSquare (regs .x10, regs .x11)).1 ∧ r' .x11 = (Model.eSquare (regs .x10, regs .x11)).2

/-- **The contract of `E::square`**, function `i` of `p` with `need` bytes of stack (its frame is 48 bytes; it
    calls `spread` and `reduce`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.ESquare
