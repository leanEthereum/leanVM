/-
  Rv64mc.Spec.Whir.RingPsi

  The contract of `verifier::ring_switch::ring_psi(value: E, g: &[E]) -> E`: `value`'s limbs in `a0`, `a1`, the
  slice `g` as a pointer and a length (`a2`, `a3`), its elements' limbs in the heap; the result's limbs in `a0`,
  `a1` are `Model.ringPsiRust`'s value.
-/

import Rv64mc.Core.Repr
import Rv64mc.Spec.Field.EMul
import Rv64mc.Spec.Field.ESquare
import Rv64mc.Model.RingSwitch

namespace Rv64mc.Spec.Whir.RingPsi

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (v : E) (gs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x10 = (Model.limbs v).1 ∧ regs .x11 = (Model.limbs v).2 ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (gs.map Model.limbs) ∧
    env.Live m (regs .x12) (Layouts.E.byteSize * gs.length)

def Post (v : E) (gs : List E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = (Model.limbs (Model.ringPsiRust v gs)).1 ∧ r' .x11 = (Model.limbs (Model.ringPsiRust v gs)).2

/-- **The contract of `ring_psi`**, function `i` of `p` with `need` bytes of stack (its frame is 64 bytes; it calls
    `E::mul` and `E::square`), for every value and slice. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ v gs, Holds env p i need (Pre env v gs) (Post v gs)

end Rv64mc.Spec.Whir.RingPsi
