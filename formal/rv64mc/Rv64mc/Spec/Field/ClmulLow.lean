/-
  Rv64mc.Spec.Field.ClmulLow

  The contract of `verifier::field::clmul_low(a, b) -> u64`: the low word of the carry-less product of `a0` and
  `a1`, as `Model.clmulLow` computes it, in `a0`.
-/

import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Spec.Field.ClmulLow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = Model.clmulLow (regs .x10) (regs .x11)

/-- **The contract of `clmul_low`**, function `i` of `p` with `need` bytes of stack (its frame is 48 bytes). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.ClmulLow
