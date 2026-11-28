/-
  LeanVM.Guest.Complete.Left

  What `GuestExecutionComplete` rests on at the deployed choices: the flags `alW`, the floor
  `2^17`, the alignment's hint-only cells and the alignment `alignA`.
-/

module

public import LeanVM.Guest.Complete.Open
public import LeanVM.Guest.Complete.HintsG
public import LeanVM.Guest.EndExecAGapsG
public import LeanVM.Guest.EndExecACurHyps
public import LeanVM.Guest.EndExecABuf
public import LeanVM.Guest.Complete.BridgeB1
public import LeanVM.Guest.Complete.JumpCellsG
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.Complete.MainCalleesHonest
public import LeanVM.Guest.Memory.GuestWf
public import LeanVM.Guest.Complete.LeftAlloc
public import LeanVM.Guest.Complete.MainFinal
public import LeanVM.Guest.Complete.CompRefG
public import LeanVM.Guest.Complete.WitCellsG
public import LeanVM.Guest.Complete.ExtraOkG
public import LeanVM.Guest.Budget.FramesG
public import LeanVM.Guest.B1.VsC.RoundsSpecA1
public import LeanVM.Guest.B1.VsC.CstA
public import LeanVM.Guest.B1.VsC.RstA
public import LeanVM.Guest.B1.VsC.CertifyA
public import LeanVM.Guest.B1.VsC.VkPM
public import LeanVM.Guest.B1.VsC.Os.LeftPost
public import LeanVM.Guest.Complete.Claims.Kids
public import LeanVM.Guest.Complete.HandLoopW
public import LeanVM.Guest.EndExecRouteG
public import LeanVM.Guest.EndExecWitPtrK
public import LeanVM.Guest.B1.VsC.VsHonDone

/-!
# The guest's execution completeness from what is left

`guestExecutionComplete_of_left : GuestLeft → GuestExecutionComplete`. `GuestLeft` is `GuestRestAt`
at `al := alW`, `k := 17`, `exOf := exA` (the alignment's hint-only cells), `A := alignA`, with the
fields the packages proved discharged: `verify_sub`'s callees (`vsCalleesCompleteA_of_rest`, `cs_completeA`, `cst_completeA`,
`rst_completeA`, `verifyKeccakCompleteA`, `openStackedCompleteA_17`), the bridge's
premises (`hintHyps_alW`: the jump cells `jumpCellsV_alignA`, the witness cells `witCells_alignA` with
the heap pointers no spine pins by the carried facts `witPtrK_carryA`, the computed hints
`compRef_alignA`), the core route's fields but the functions off it (`route_alW`, the routed functions'
data by `tableOf_cfOk`), the reference run's frames (`refFrames_alW`), the hint-only cells
(`extraOk_exA`), the cursor facts (`curHyps_of`), the address hints (`addrReady_alignA`), the buffer
hints (`bufHint_alignA`, `dynPow_left`), the frame hints (`frameHint_alignA`, `progOk_guest`), the
callees of `main` (`mainCalleesOpenA`: the claim lists, the raw signatures, `da_verify`,
`aggregate_claims` and the children's claim lists at the honest coverage table), `main`'s window
(`mainWindowFromCallees`), its hand facts (`mainHand_alW`, `mainCycles_alW`) and the frames within
the certificates' (`FramesWithin`: `fs_within_fsW`, `B2C.fs_tailKey_le`). `verify_sub`'s windows (`vsWindows_alW`, from its honest context at every accepted child,
`vsHonPartsEx_alW`). One field is left: `off`, the functions off the core route.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Completeness LeanVM.Guest.Budget LeanVM.Guest.EndExec LeanVM.Guest.Mode
open LeanVM.Prover.Exec
open LeanVM.Guest.Bridge (FnAl alignA)

@[expose] public section

/-- **What `GuestExecutionComplete` rests on, at the deployed choices.** -/
structure GuestLeft : Prop where
  /-- route: a certificate with its facts for each function off the core route, and its core data's
  checks. -/
  off : ∃ (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun),
    EndExec.OffOk CoreMode.corePacks CoreMode.offSigs offK Toff ∧ ∀ Cf ∈ Toff, CoreMode.CfOk Cf

/-- **`GuestRest` from what is left.** -/
theorem guestRest_of_left (h : GuestLeft) : GuestRest := by
  have hH : HintHyps (lay alW) (refD alW) alignA := hintHyps_alW (witCells_alignA witPtrK_carryA) compRef_alignA
  have hC : CurHyps (lay alW) (refD alW) alignA := curHyps_of progAl_alignA Bridge.AllocChk.allocFnChk_guest
  have hB : BufHint (lay alW) (refD alW) alignA := bufHint_alignA hH rfl rfl rfl rfl dynPow_left
  have hF : FrameHint (lay alW) (refD alW) alignA := frameHint_alignA hH rfl rfl rfl rfl rfl EndExec.progOk_guest
  have hAr : AddrReady (lay alW) (refD alW) alignA := addrReady_alignA hH rfl rfl rfl rfl
  exact ⟨alW, 17, alignA, le_rfl, by norm_num,
    { vsWindows := VsC.vsWindows_alW
      vsCallees := VsC.vsCalleesCompleteA_of_rest (by norm_num) (VsC.cs_completeA (by norm_num))
        (VsC.cst_completeA (by norm_num)) (VsC.rst_completeA _) (B1.VerifySub.verifyKeccakCompleteA (by norm_num))
        VsC.openStackedCompleteA_17
      mainCallees := mainCalleesOpenA
      mainWindow := mainWindowFromCallees
      hand := mainHand_alW
      framesWithin := ⟨fs_within_fsW, fun _ hg => hg, B2C.fs_tailKey_le⟩
      cycles := mainCycles_alW
      extraOk := extraOk_exA
      refFrames := refFrames_alW
      hints := hH
      cur := hC
      bufHint := hB
      frameHint := hF
      addrReady := hAr
      route := route_alW hH hC hB hF hAr h.off }⟩

/-- **`GuestExecutionComplete` from what is left.** -/
theorem guestExecutionComplete_of_left (h : GuestLeft) : GuestExecutionComplete :=
  guestExecutionComplete_of_rest (guestRest_of_left h)

end

end LeanVM.Guest.Complete
