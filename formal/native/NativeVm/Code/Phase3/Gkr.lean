module

public import NativeVm.Code.Phase3.GkrLayers

/-!
# Phase 3a: the bus's GKR walk

`gkr_spec`: `gkrCode` (`NativeVm.Code.Phase3.GkrCode`) runs `Model.verifyGkrGrandProducts depth`,
`depth` read from `depthR`: the count root at `countR`, the point at `pointR`, the trees' values at
`treeR`; it writes only `pointR`, `treeR`, `countR` and `tmpR` (and the transcript's words), or fails
exactly where the model rejects.

The proof follows the code's blocks, a module each: the model's facts (`GkrModel`: every grind of
the walk is of `0` bits), the words and frames (`GkrBase`), the kernels on `EW` (`GkrKern`), a step's
start (`GkrComb`), a sumcheck round (`GkrMsg`, `GkrRounds`) and its loop (`GkrSumcheck`), the
children (`GkrChild`, `GkrChildren`), the step's end (`GkrY`), the step (`GkrStep`), the walk's
start and loop (`GkrLayers`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

/-- **`gkrCode` runs `verifyGkrGrandProducts depth`.** -/
theorem gkr_spec {env : Env} {inp : Input} {t : TState} {s : QState} {depth : Nat}
    (h : CodeRel env t s) (hi : Inputs env inp s.mem) (hd : depth < 64)
    (hdw : NatAt s.mem (depthR.at env.work) depth) :
    WP gkrCode s
      (fun s' ↦ ∃ r t', (verifyGkrGrandProducts depth).run t = some (r, t') ∧ CodeRel env t' s' ∧
        EWAt s'.mem (countR.at env.work) r.1 ∧ r.2.1.size = depth ∧
        EWArr s'.mem (pointR.at env.work) r.2.1 ∧ r.2.2.size = 3 ∧
        EWArr s'.mem (treeR.at env.work) r.2.2 ∧
        Step3 env allRegs [pointR, treeR, countR, tmpR] s s')
      (fun s' ↦ (verifyGkrGrandProducts depth).run t = none ∧
        Step3 env allRegs [pointR, treeR, countR, tmpR] s s') := by
  have hdw' : NatAt s.mem (wd env.work gD) depth := hdw
  unfold gkrCode
  refine WP.then (WP.mono (readTo_spec (r := treeR) (k := gTr) (by gok3) (by gomega) (by gomega) h hi)
    (fun _ h ↦ h) (fun s' ⟨hn, hst⟩ ↦ ⟨verifyGkr_none1 hn, hst.gall.mono (fun _ h ↦ h) (by simp)⟩))
    fun s1 ⟨shared, t1, hr1, h1, hsh, hst1⟩ ↦ ?_
  have hi1 := hi.step3 (by gok3_tac) hst1 h.rdi
  refine WP.then (WP.mono (readTo_spec (r := countR) (k := gCt) (by gok3) (by gomega) (by gomega) h1
      hi1) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨verifyGkr_none2 hr1 hn, hst1.gtrans hst (by simp) (by simp)⟩))
    fun s2 ⟨count, t2, hr2, h2, hct, hst2⟩ ↦ ?_
  have hi2 := hi1.step3 (by gok3_tac) hst2 h1.rdi
  have f2 : Step3 env allRegs gkrWs s s2 := hst1.gtrans hst2 (by simp [gkrWs]) (by simp [gkrWs])
  refine WP.then (WP.mono (initC_spec h2 hi2 (hsh.congr (by gsame hst2, hi1)) hct
      (NatAt.gkeep (NatAt.gkeep hdw' (by gsame hst1, hi)) (by gsame hst2, hi1)))
      (fun _ h ↦ h) (fun _ h ↦ h.elim))
    fun s3 ⟨htr, ho, hrem, h14, hw3⟩ ↦ ?_
  refine layersC_spec hd ⟨depth, ⟨#[shared, shared, count], #[]⟩, t2, le_rfl,
    h2.wrote3 hi2 (by gok3_tac) hw3, hi2.step3 (by gok3_tac) hw3.step h2.rdi, hrem, h14,
    NatAt.gkeep (NatAt.gkeep (NatAt.gkeep hdw' (by gsame hst1, hi)) (by gsame hst2, hi1))
      (by gsamew hw3, hi2),
    ho, htr, rfl, fun i hi' ↦ absurd hi' (by simp), by simp,
    hct.congr (by gsamew hw3, hi2), f2.into hw3.step (by unfold gkrWs; gwithin_tac),
    verifyGkr_run hr1 hr2⟩

end NativeVm.Code.P3
