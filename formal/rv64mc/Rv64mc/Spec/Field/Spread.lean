/-
  Rv64mc.Spec.Field.Spread

  The contract of `verifier::field::spread(a: u64) -> u128`: the bits of `a0` spread to the even positions, as
  `Model.spread` computes it, returned in `a0` (low) and `a1` (high). A leaf without a frame.
-/

import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Spec.Field.Spread

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = lo128 (Model.spread (regs .x10)) ∧ r' .x11 = hi128 (Model.spread (regs .x10))

/-- **The contract of `spread`**, function `i` of `p` with `need` bytes of stack (it has no frame). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.Spread
