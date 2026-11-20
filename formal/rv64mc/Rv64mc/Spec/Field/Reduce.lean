/-
  Rv64mc.Spec.Field.Reduce

  The contract of `verifier::field::reduce(p: u128) -> u64`: `p` (low word in `a0`, high in `a1`) reduced modulo
  `x^64 + x^4 + x^3 + x + 1`, as `Model.reduce` computes it, in `a0`. A leaf without a frame.
-/

import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Spec.Field.Reduce

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = Model.reduce (regs .x11 ++ regs .x10)

/-- **The contract of `reduce`**, function `i` of `p` with `need` bytes of stack (it has no frame). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Field.Reduce
