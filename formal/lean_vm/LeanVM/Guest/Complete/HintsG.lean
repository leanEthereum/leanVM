/-
  LeanVM.Guest.Complete.HintsG

  The hint bridge's premises and the reference run's frames at the deployed alignment, from the
  jump cells on valid runs.
-/

module

public import LeanVM.Guest.EndExecHintsG
public import LeanVM.Guest.Complete.RefFramesCore

/-!
# The bridge's premises and the frames at the deployed alignment

On b2c's layout at the budget's flags `alW` and the deployed alignment `alignA`, the jump cells on
every valid reference run (`JumpCellsV`) give both the bridge's `JumpCellsAt` (`hintHyps_alignV`,
with `WitCells` and `CompRef`) and the reference run's frames (`refFrames_alignA`, refframes'
`refFrames_core`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Semantics LeanVM.Guest
open LeanVM.Guest.Bridge (alignA)

public section

variable {D : Ref → RefD}

/-- **The bridge's premises at the deployed alignment**, from the jump cells on valid runs. -/
theorem hintHyps_alignV (hJ : JumpCellsV ⟨B2C.fs, Memory.alW, B2C.H, B2C.C, B2C.cert⟩ D alignA)
    (hW : WitCells ⟨B2C.fs, Memory.alW, B2C.H, B2C.C, B2C.cert⟩ D alignA)
    (hC : CompRef ⟨B2C.fs, Memory.alW, B2C.H, B2C.C, B2C.cert⟩ D alignA) :
    HintHyps ⟨B2C.fs, Memory.alW, B2C.H, B2C.C, B2C.cert⟩ D alignA :=
  hintHyps_alignA rfl hJ.toAt hW hC

/-- **The reference run's frames at the deployed alignment**, from the jump cells on valid runs. -/
theorem refFrames_alignA (hJ : JumpCellsV ⟨B2C.fs, Memory.alW, B2C.H, B2C.C, B2C.cert⟩ D alignA) :
    ∀ r, RefH ⟨B2C.fs, Memory.alW, B2C.H, B2C.C, B2C.cert⟩ (D r) r → ValidExecution guestProgram r.input r.exec →
      FramesIn guestProgram r.img r.n ∧ Mode.KeccakFramesAligned guestProgram r.img r.n :=
  refFrames_core progAl_alignA mainAt_alignA hJ code_alignA

end

end LeanVM.Guest.EndExec
