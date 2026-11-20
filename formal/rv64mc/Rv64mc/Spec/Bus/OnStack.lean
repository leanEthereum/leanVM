/-
  Rv64mc.Spec.Bus.OnStack

  The contract of `ColumnClaim::on_stack(&self, layout: &Layout) -> Option<StackClaim>`: the result's slot (`sret`)
  in `a0`, `self` in `a1`, `layout` in `a2`, of which it reads `placements` and `stack_log`. It writes
  `Model.onStackRust`'s answer at `sret` (`OptStackClaimAt`): `None` for a column nothing commits, else the
  column's placement's `Eq` weight at its stacked point, in a fresh `Vec`, and the claim's value. The slot and
  `self` are apart (Rust's `&mut` and `&`).
-/

import Rv64mc.Spec.Bus.Repr
import Rv64mc.Spec.Whir.Basic

namespace Rv64mc.Spec.Bus.OnStack

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters LeanVM.Protocol.Verifier Rv64mc.Spec.Layout

/-- The placements `layout.placements` holds, as the elements of its `Vec`, live. -/
def PlacementsAt (env : Env) (m : MachineState) (layout : Word) (ps : List (Option Model.PlacementRust)) : Prop :=
  ElemsAt Layouts.OptionPlacement.byteSize OptPlacementAt m
      (vecPtr m (layout + BitVec.ofNat 64 Layouts.Layout.placements)) ps ∧
    vecLen m (layout + BitVec.ofNat 64 Layouts.Layout.placements) = BitVec.ofNat 64 ps.length ∧
    env.Live m (vecPtr m (layout + BitVec.ofNat 64 Layouts.Layout.placements))
      (Layouts.OptionPlacement.byteSize * ps.length)

def Pre (env : Env) (l : Model.LayoutRust) (c : ColumnClaim) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.OptionStackClaim.byteSize ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.ColumnClaim.byteSize ∧
    env.Owned m (regs .x2) (regs .x12) Layouts.Layout.byteSize ∧
    (∀ b, InRange (regs .x10) Layouts.OptionStackClaim.byteSize b → ¬ InRange (regs .x11) Layouts.ColumnClaim.byteSize b) ∧
    ColumnClaimAt env m (regs .x11) c ∧ PlacementsAt env m (regs .x12) l.placements ∧
    m.getMem (regs .x12 + BitVec.ofNat 64 Layouts.Layout.stack_log) = BitVec.ofNat 64 l.stackLog ∧
    l.stackLog < 2 ^ 64 ∧ ∀ q, l.placements.getD c.column none = some q → q.variableCount < 2 ^ 64

def Post (env : Env) (l : Model.LayoutRust) (c : ColumnClaim) (regs : Reg → Word) (m : MachineState)
    (_r' : Reg → Word) (m' : MachineState) : Prop :=
  OptStackClaimAt env m m' (regs .x10) (Model.onStackRust l c)

/-- **The contract of `on_stack`**, function `i` of `p` with `need` bytes of stack (its frame is 32 bytes; it calls
    `stack_point` and the bounds check's panic), for every layout and claim. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ l c, Holds env p i need (Pre env l c) (Post env l c) (Whir.SretOut Layouts.OptionStackClaim.byteSize)

end Rv64mc.Spec.Bus.OnStack
