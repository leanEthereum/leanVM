/-
  Rv64mc.Spec.Whir.Frobenius8

  The contract of `verifier::ring_switch::frobenius_8(value: E, p: usize) -> E`: `value`'s limbs in `a0`, `a1`, `p`
  in `a2`; the result's limbs in `a0`, `a1` are `Model.frobenius8Rust`'s value, `value` squared `8 p` times, for a
  `p` whose `8 p` does not wrap (`ring_target` passes `p < 8`).
-/

import Rv64mc.Spec.Field.ESquare
import Rv64mc.Model.RingSwitch

namespace Rv64mc.Spec.Whir.Frobenius8

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (v : E) (regs : Reg → Word) (_m : MachineState) : Prop :=
  regs .x10 = (Model.limbs v).1 ∧ regs .x11 = (Model.limbs v).2 ∧ 8 * (regs .x12).toNat < 2 ^ 64

def Post (v : E) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = (Model.limbs (Model.frobenius8Rust v (regs .x12).toNat)).1 ∧
    r' .x11 = (Model.limbs (Model.frobenius8Rust v (regs .x12).toNat)).2

/-- **The contract of `frobenius_8`**, function `i` of `p` with `need` bytes of stack (its frame is 16 bytes; it
    calls `E::square`), for every value. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := ∀ v, Holds env p i need (Pre v) (Post v)

end Rv64mc.Spec.Whir.Frobenius8
