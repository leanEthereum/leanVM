/-
  LeanVM.Guest.EndExecRouteG

  The core route's fields of the end (`Complete.RouteGaps`) at the deployed choices, from the
  functions off the route and the core data's checks.
-/

module

public import LeanVM.Guest.Complete.Open
public import LeanVM.Guest.EndExecResNzD
public import LeanVM.Guest.EndExecCoreGhostD
public import LeanVM.Guest.EndExecAssemble
public import LeanVM.Guest.EndExecAGaps
public import LeanVM.Guest.CoreMode.Fam.EntA
public import LeanVM.Guest.CoreMode.Gen.Certs
public import LeanVM.Guest.CoreMode.Gen.CertsTerm
public import LeanVM.Guest.CoreMode.Gen.Certs.CfOk

/-!
# The core route at the deployed choices

`route_alW`: `GuestLeft.route`'s statement (`RouteGaps` at `RefOf alW`, the hint tracks over
`YAlloc`, `alignA`) from the hint bridge's premises (`HintHyps`), the allocation track's (`CurHyps`,
`BufHint`, `FrameHint`, `AddrReady`, as `ExecGaps.ofHintsAlloc` takes them) and what the core route leaves: a certificate with its facts for each function off the route
(`OffOk`) and their core data's checks (`CfOk`, the routed functions' by `tableOf_cfOk`). The certificates are `coreAssembled`'s; the frames by
`frame_core` (`CoreHonAll` by `coreHonAll_ghost` at `ghostOk_guest`, `UsedNextAll` by
`usedNextAll_of`); the residuals by `res_of_track` from `resTrack_nzOnly` (every residual a listed
nonzero value, `nzOnly_all`, each nonzero, `nzs_okA`); the termination facts by `term_of_nodeA` from
`coreTermNodeA`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec LeanVM.Guest.Mode
open LeanVM.Prover.Exec
open LeanVM.Guest.Bridge (alignA alignA_of)

public section

/-- **The core route's fields at the deployed choices**, given the functions off the route and the
core data's checks. -/
theorem route_alW (hH : HintHyps (lay alW) (refD alW) alignA)
    (hC : CurHyps (lay alW) (refD alW) alignA) (hB : BufHint (lay alW) (refD alW) alignA)
    (hF : FrameHint (lay alW) (refD alW) alignA) (hAr : AddrReady (lay alW) (refD alW) alignA)
    (hoff : ∃ (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun),
      OffOk CoreMode.corePacks CoreMode.offSigs offK Toff ∧ ∀ Cf ∈ Toff, CoreMode.CfOk Cf) :
    ∃ (Ks : List Mode.Cert) (Km : Mode.Cert) (E0 : Mode.Env) (Ct : Ref → Mode.Cts)
      (Q : Ref → Mode.Cert → ℕ → St → Prop),
      RouteGaps (RefOf alW) (YH (lay alW) (refD alW) alignA (YAlloc (lay alW) (refD alW) alignA)) Ks Km E0 Ct Q := by
  obtain ⟨offK, Toff, hoff, hcf⟩ := hoff
  have hasm := CoreMode.coreAssembled offK Toff hoff
  have hRH : ∀ r, RefOf alW r → RefH (layB alW) (refD alW r) r := fun _ h ↦ refH_refD h
  have hA : AllocTrack (RefOf alW) (YAlloc (lay alW) (refD alW) alignA) :=
    allocTrack_ofHint hH hRH hasm.2.2.1 (mainA_of rfl) hC hB hF hAr
  have hAX : ∀ f j, B2C.idxOf f = some j → (alignA f).X = Bridge.ctxOf j := fun _ _ h ↦ by
    rw [alignA_of h]; rfl
  have hon : CoreHonAll (RefOf alW) (tableOf CoreMode.corePacks Toff) (certsOf CoreMode.corePacks CoreMode.offSigs offK)
      (XOf (YH (lay alW) (refD alW) alignA (YAlloc (lay alW) (refD alW) alignA))) :=
    coreHonAll_ghost hasm.1 (fun _ h ↦ h) hasm.2.2.2.2 hH hRH entIdx_alignA hAX (CoreMode.tableOf_cfOk hcf) ghostOk_guest
  exact ⟨_, _, _, _, _,
    { certs := hasm.1
      main := hasm.2.2.1
      frame := frame_core hasm.1 hasm.2.1 hon (usedNextAll_of hH hA hRH)
      ctMain := ctMain_core hasm.2.2.2.1
      res := res_of_track hasm.1 (fun _ h ↦ h) hasm.2.2.2.2 hH hRH
        (resTrack_nzOnly hasm.1 (fun _ h ↦ h) hH hRH entIdx_alignA (nzOnly_all hoff) nzs_okA)
      term := termRef_of_sub (term_or_filter _)
        (term_of_nodeA hasm.1 (fun _ h ↦ (List.mem_filter.1 h).1) hasm.2.2.2.2 hH hRH
          (CoreMode.coreTermNodeA offK Toff hoff entIdx_alignA hRH)) }⟩

end

end LeanVM.Guest.Complete
