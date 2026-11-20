/-
  Rv64mc.Spec.Multilinear.StackPoint

  The contract of `Placement::stack_point(&self, point: &[E], stack_log: usize) -> Vec<E>`: the result's header at
  `sret` (`a0`), the placement by value (`variables` in `a1`, `index` in `a2`), the point as a slice (`a3`, `a4`, its
  elements' limbs in the heap), `stack_log` in `a5`; the result is `Model.PlacementRust.stackPoint`'s, in a fresh
  block (`FreshVecE`).
-/

import Rv64mc.Spec.Multilinear.Basic
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.StackPoint

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The placement the registers hold. -/
def placement (regs : Reg → Word) : Model.PlacementRust := ⟨(regs .x11).toNat, regs .x12⟩

def Pre (env : Env) (pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧
    SliceArgs EListAt m (regs .x13) (regs .x14) (pt.map Model.limbs) ∧
    env.Live m (regs .x13) (Layouts.E.byteSize * pt.length)

def Post (env : Env) (pt : List E) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  FreshVecE env m m' (regs .x10) ((placement regs).stackPoint pt (regs .x15).toNat)

/-- **The contract of `stack_point`**, function `i` of `p` with `need` bytes of stack (its frame is 96 bytes; it
    calls `selector_point` and `<[&[E]]>::concat`), for every point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ pt, Holds env p i need (Pre env pt) (Post env pt) (Whir.SretOut Layouts.Vec.byteSize)

end Rv64mc.Spec.Multilinear.StackPoint
