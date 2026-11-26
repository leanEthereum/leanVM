/-
  Rv64mc.Spec.Field.KInv

  The contract of `K::inv`: the inverse in `K` of `a0` (zero to zero), as `Model.kInv` computes it by Itoh-Tsujii,
  in `a0`. `Model.kInv_eq` makes it the inverse in `K`.
-/

import Rv64mc.Spec.Field.Spread
import Rv64mc.Spec.Field.BaseMul

namespace Rv64mc.Spec.Field.KInv

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = Model.kInv (regs .x10)

/-- **The contract of `K::inv`**, function `i` of `p` with `need` bytes of stack (its frame is 32 bytes; it calls
    `spread`, `reduce` and `base_mul`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.KInv
