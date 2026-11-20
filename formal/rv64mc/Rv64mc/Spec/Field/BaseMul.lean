/-
  Rv64mc.Spec.Field.BaseMul

  The contract of `verifier::field::base_mul(left, right) -> u64`: the product in `K` of `a0` and `a1`, as
  `Model.baseMul` computes it (`reduce(clmul(left, right))`), in `a0`. `Model.baseMul_eq` makes it the product in
  `K`.
-/

import Rv64mc.Spec.Field.Clmul
import Rv64mc.Spec.Field.Reduce

namespace Rv64mc.Spec.Field.BaseMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = Model.baseMul (regs .x10) (regs .x11)

/-- **The contract of `base_mul`**, function `i` of `p` with `need` bytes of stack (its frame is 16 bytes; it
    calls `clmul` and tail-calls `reduce`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.BaseMul
