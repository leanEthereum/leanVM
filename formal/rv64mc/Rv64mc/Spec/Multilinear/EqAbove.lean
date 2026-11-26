/-
  Rv64mc.Spec.Multilinear.EqAbove

  The contract of `Placement::eq_above(&self, point: &[E]) -> E`: the placement by value (`variables` in `a0`,
  `index` in `a1`), the point as a slice (`a2`, `a3`, its elements' limbs in the heap); the result's limbs in `a0`,
  `a1` are `Model.PlacementRust.eqAbove`'s value. A point shorter than `variables` does not return
  (`slice_index_fail`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.EqAbove

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The placement the registers hold. -/
def placement (regs : Reg → Word) : Model.PlacementRust := ⟨(regs .x10).toNat, regs .x11⟩

def Pre (env : Env) (pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x12) (regs .x13) (pt.map Model.limbs) ∧
    env.Live m (regs .x12) (Layouts.E.byteSize * pt.length)

def Post (pt : List E) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  ∀ v, (placement regs).eqAbove pt = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `eq_above`**, function `i` of `p` with `need` bytes of stack (its frame is 64 bytes; it calls
    `selector_point` and `slice_index_fail`, and tail-calls `eq_eval`), for every point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ pt, Holds env p i need (Pre env pt) (Post pt)

end Rv64mc.Spec.Multilinear.EqAbove
