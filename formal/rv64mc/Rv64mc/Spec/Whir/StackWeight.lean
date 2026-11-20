/-
  Rv64mc.Spec.Whir.StackWeight

  The contract of `StackWeight::evaluate(&self, x: &[E]) -> E` (`lib.rs`): `self` in `a0`, `x` as a pointer and a
  length in `a1`, `a2`; the result's limbs in `a0`, `a1` are `Model.StackWeightRust.evaluate`'s value wherever it has
  one. The weight sits at `self` as `StackWeightAt` says: `Eq` and `Ring` by their niche tags and their fields at
  `f0`, `PlacedRing` by its placement and its ring weight.
-/

import Rv64mc.Spec.Whir.RingWeight
import Rv64mc.Model.Whir

namespace Rv64mc.Spec.Whir.StackWeight

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingWeight

/-- **The `StackWeight` `w` at `a`**, its buffers live. -/
def StackWeightAt (env : Env) (m : MachineState) (a : Word) : Model.StackWeightRust → Prop
  | .eq point => m.getMem (a + BitVec.ofNat 64 Layouts.StackWeight.tagOffset) =
        BitVec.ofNat 64 Layouts.StackWeight.Eq.tag ∧
      EVecAt env m (a + BitVec.ofNat 64 Layouts.StackWeight.Eq.f0) point
  | .ring w => m.getMem (a + BitVec.ofNat 64 Layouts.StackWeight.tagOffset) =
        BitVec.ofNat 64 Layouts.StackWeight.Ring.tag ∧
      RingWeightAt env m (a + BitVec.ofNat 64 Layouts.StackWeight.Ring.f0) w
  | .placedRing pl w =>
      m.getMem (a + BitVec.ofNat 64 (Layouts.StackWeight.PlacedRing.f0 + Layouts.Placement.variables)) =
        BitVec.ofNat 64 pl.variableCount ∧ pl.variableCount < 2 ^ 64 ∧
      m.getMem (a + BitVec.ofNat 64 (Layouts.StackWeight.PlacedRing.f0 + Layouts.Placement.index)) = pl.index ∧
      RingWeightAt env m (a + BitVec.ofNat 64 Layouts.StackWeight.PlacedRing.f1) w

def Pre (env : Env) (w : Model.StackWeightRust) (x : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.StackWeight.byteSize ∧ StackWeightAt env m (regs .x10) w ∧
    ESlice env m (regs .x11) (regs .x12) x

def Post (w : Model.StackWeightRust) (x : List E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (_m' : MachineState) : Prop :=
  ∀ v, w.evaluate x = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `StackWeight::evaluate`**, function `i` of `p` with `need` bytes of stack, for every weight
    and point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ w x, Holds env p i need (Pre env w x) (Post w x)

end Rv64mc.Spec.Whir.StackWeight
