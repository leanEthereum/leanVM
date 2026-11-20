/-
  Rv64mc.Spec.Keccak.InstanceWeights

  The contract of `verifier::keccak::instance_weights(s: E) -> Vec<E>`: the result's slot (`sret`) in `a0`, `s`'s limbs
  in `a1`, `a2`. The slot holds a `Vec` of `Model.instanceWeightsRust s`'s limbs (sixteen, one per `RMFE_EMBED` entry),
  in a buffer the call allocated; the call writes the slot (`Out`). The stack pointer is 8-aligned: the code stores a
  `u32` into its frame and reads it back by `lw` beside doubleword stores.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.KeccakGkr

namespace Rv64mc.Spec.Keccak.InstanceWeights

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (s : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x11 = (Model.limbs s).1 ∧ regs .x12 = (Model.limbs s).2 ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ (regs .x2).toNat % 8 = 0

def Post (env : Env) (s : E) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  ∃ ptr cap, VecAt EListAt m' (regs .x10) ptr cap ((Model.instanceWeightsRust s).map Model.limbs) ∧
    env.Fresh m m' ptr (Layouts.E.byteSize * cap)

/-- What it writes besides its stack and allocations: the result's slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Vec.byteSize b

/-- **The contract of `instance_weights`**, function `i` of `p` with `need` bytes of stack (its frame is 528 bytes;
    it calls `E::mul`, `alloc`, `Vec::<E>::reserve`, the bit-filtered sum and `handle_error`), for every `s`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ s, Holds env p i need (Pre env s) (Post env s) Out

end Rv64mc.Spec.Keccak.InstanceWeights
