/-
  Rv64mc.Spec.Field.Powers

  The contract of `verifier::field::powers(base: E, count) -> Vec<E>`: the result's slot (`sret`) in `a0`, `base`'s
  limbs in `a1`, `a2`, `count` in `a3`; the slot holds a fresh `Vec` of `Model.powersM`'s powers `1, base, ...`.
-/

import Rv64mc.Spec.Multilinear.Basic
import Rv64mc.Spec.Whir.Basic

namespace Rv64mc.Spec.Field.Powers

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize

def Post (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  Multilinear.FreshVecE env m m' (regs .x10)
    ((Model.powersM (regs .x11, regs .x12) (regs .x13).toNat).map Model.ofLimbsW)

/-- **The contract of `powers`**, function `i` of `p` with `need` bytes of stack (its frame is 96 bytes; it calls
    `alloc`, `E::mul` and `handle_error`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (Pre env) (Post env) (Whir.SretOut Layouts.Vec.byteSize)

end Rv64mc.Spec.Field.Powers
