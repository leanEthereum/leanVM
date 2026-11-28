/-
  LeanVM.Guest.Complete.JumpCellsG

  The jump cells on every reference run at the deployed alignment, and with them the reference run's
  frames and the hint bridge's jump cells.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsOf
public import LeanVM.Guest.EndExecChain
public import LeanVM.Guest.Complete.HintsG
public import LeanVM.Guest.Complete.Open

/-!
# The jump cells at the deployed alignment

`jumpCellsV_alignA`: on b2c's layout at any flags `al`, every reference run of the honest tree has
its jump cells at `alignA` (`JumpCellsV`), by `Bridge.jumpCells_ofA` on the reference's memory, which
covers the honest writes (`RefH.img`, `HonestX.covers`), the chained `match`es' arms by
`chainArm_of_one` (`chainOneB_true`, the kernel over the plumbing). It needs neither `r.Ok` nor the
run's validity. At the budget's flags `alW`: `refFrames_alW : RefFrames alW` (`GuestRestAt.refFrames`)
and `hintHyps_alW`, `GuestRestAt.hints` from `WitCells` and `CompRef`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Guest.Bridge (alignA)

public section

/-- **The jump cells on every reference run**, at the deployed alignment and any flags. -/
theorem jumpCellsV_alignA {al : String → Bool} {D : Ref → RefD} :
    JumpCellsV ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D alignA := by
  intro r hR _ pc fp done e st htr
  obtain ⟨rd, hH, hX⟩ := hR.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun q hq ha ↦ (hR.img q.1).trans (hX.covers q hq ha)
  exact Bridge.jumpCells_ofA hR.name hH hcov (chainArm_of_one chainOneB_true) htr

/-- **The reference run's frames** at the budget's flags (`GuestRestAt.refFrames`). -/
theorem refFrames_alW : RefFrames alW :=
  refFrames_alignA jumpCellsV_alignA

/-- **The hint bridge's premises** at the budget's flags (`GuestRestAt.hints`), its jump cells
discharged. -/
theorem hintHyps_alW (hW : WitCells (lay alW) (refD alW) alignA) (hC : CompRef (lay alW) (refD alW) alignA) :
    HintHyps (lay alW) (refD alW) alignA :=
  hintHyps_alignV jumpCellsV_alignA hW hC

end

end LeanVM.Guest.Complete
