/-
  Rv64mc.Spec.Layout.Committed

  The contract of `Layout::committed(&self, column) -> Result<Placement, VerifierError>`, which the compiled code
  calls with the result's slot (`sret`) in `a0`, `self.placements`' pointer and length in `a1`, `a2` (the one field
  it reads), and `column` in `a3`: it writes `Model.LayoutRust.committed`'s answer at `sret`
  (`ResultPlacementAt`), `Err(CommittedSize)` for a column out of range or with no placement.
-/

import Rv64mc.Spec.Layout.Repr

namespace Rv64mc.Spec.Layout.Committed

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A leaf without a frame. -/
def need : Nat := 0

/-- The placements as a slice, and `sret` a caller's to write. -/
def Pre (env : Env) (ps : List (Option Model.PlacementRust)) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs (ElemsAt Layouts.OptionPlacement.byteSize OptPlacementAt) m (regs .x11) (regs .x12) ps ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.ResultPlacement.byteSize

def Post (ps : List (Option Model.PlacementRust)) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ResultPlacementAt m' (regs .x10) (ps.getD (regs .x13).toNat none)

/-- It writes the result's slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.ResultPlacement.byteSize b

/-- **The contract of `Layout::committed`**, function `i` of `p`, for every list of placements. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ ps, Holds env p i need (Pre env ps) (Post ps) Out

end Rv64mc.Spec.Layout.Committed
