/-
  Rv64mc.Spec.Field.EMul

  The contract of `<E as Mul>::mul`: `self` (limbs in `a0`, `a1`) times `rhs` (`a2`, `a3`), as `Model.eMul` computes
  it on limbs, in `a0`, `a1`. `Model.eMul_eq` makes it the product in `E`: `eMul (limbs x) (limbs z) = limbs (x * z)`.
-/

import Rv64mc.Spec.Field.Clmul
import Rv64mc.Spec.Field.Reduce

namespace Rv64mc.Spec.Field.EMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The stack it needs: its frame (80 bytes) and its deepest callee's (`clmul`). -/
def need : Nat := 80 + Clmul.need

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = (Model.eMul (regs .x10, regs .x11) (regs .x12, regs .x13)).1 ∧
    r' .x11 = (Model.eMul (regs .x10, regs .x11) (regs .x12, regs .x13)).2

/-- **The contract of `E::mul`**, function `i` of `p`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.EMul
