/-
  Rv64mc.Spec.Field.Clmul

  The contract of `verifier::field::clmul(a, b) -> u128`: the carry-less product of `a0` and `a1`, as `Model.clmul`
  computes it, returned in `a0` (low) and `a1` (high).
-/

import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Spec.Field.Clmul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The stack it needs: its frame (80 bytes) and `clmul_low`'s (48). -/
def need : Nat := 128

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = lo128 (Model.clmul (regs .x10) (regs .x11)) ∧ r' .x11 = hi128 (Model.clmul (regs .x10) (regs .x11))

/-- **The contract of `clmul`**, function `i` of `p`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.Clmul
