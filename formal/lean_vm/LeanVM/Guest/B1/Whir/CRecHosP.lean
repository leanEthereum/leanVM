/-
  LeanVM.Guest.B1.Whir.CRecHosP

  `open_stacked` placed within its bound by a tree popping its levels' `level_queries` entries.
-/

module

public import LeanVM.Guest.B1.Whir.CRecHos
public import LeanVM.Guest.B1.Place.ArmPops
public import LeanVM.Guest.B1.Place.OsFinal

/-!
# `open_stacked_completeAtBP_Spec`

The arm's node at the honest data of the run (`HonRun.osHonest`, `open_stacked_completeAtOT_of`) pops its levels' `osLvPops` (`arm_pops`, the arm's body mute in `armS`: `armMute_all`), which are the run's `lvPops`. `verify_sub_completeBTS`: `verify_sub_completeBTP` with its `hos` so discharged (`vs_hos_of`), on segments whose query steps are the child's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`open_stacked` is complete placed within its bound by a tree popping its levels' `level_queries`
entries.** -/
theorem open_stacked_completeAtBP : open_stacked_completeAtBP_Spec := by
  intro μ r h1 h2 h3 h4 fs cert κ Bnd hrf hcons hκ hleaf hfs S root target cur tabs xs os w s' roots' hrun hnz
    hcaps Lin hLin
  obtain ⟨cfg, Ls, hR, hst⟩ := Whir.honRunS_of h1 h2 h3 h4 hrun hnz hcaps
  have hm : μ - Whir.minOpenLog < 11 := hR.m11
  obtain ⟨fn, hf, -, h⟩ := Arm.open_stacked_completeAtOT_of (Bd := some Bnd) level_residual_completeAt h2 h3 h4
    hrf hcons hκ (fun _ hB ↦ by cases hB; exact hleaf) (fun _ _ ↦ helperBounds fs cert κ hrf hcons hκ hfs)
    (hR.osHonest (cur := cur) (tabs := tabs)) hLin
  obtain ⟨fn', hf', hmu⟩ := Arm.armMute_all hm
  rw [← Whir.openName_eq hm, hf, Option.some.injEq] at hf'
  subst hf'
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, hn _ rfl, ho, hw, hd, fun rd hl hmem ↦ ?_⟩
  obtain ⟨t, ht, hT⟩ := hr rd hl hmem
  refine ⟨t, ht, cfg, Ls, hR, hst, ?_⟩
  have hP : Arm.osLvPops (hR.osHonest (cur := cur) (tabs := tabs)) = Whir.lvPops Ls μ r := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := hR.osHonest_fields (cur := cur) (tabs := tabs)
    funext l
    simp only [Arm.osLvPops, Whir.lvPops, e1, e2, e3, e4, e5]
  rw [Arm.arm_pops hm hR.r4 hf hmu ht.2.1 hT, hP]
  exact SameStreams.refl _

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_sub` is complete on an honest child within its own bound by a node popping `childHints` past its
advised sizes**, stream by stream, on segments whose query steps are the child's (`child_segments_steps`). -/
theorem verify_sub_completeBTS {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (hS : SegSteps S)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ vsTsAny fs W Bvk S.μs S.rate t ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bytecode seed c).drop 4))
      (vsBoundAt W Bvk S.μs S.rate) :=
  verify_sub_completeBTP hbl hrf hcons W hκ hvk S sqE outE Lin hst hexp hout
    fun bs pv ↦ vs_hos_of open_stacked_completeAtBP S hS hrz (by omega) hrf hcons W bs sqE pv

end
end LeanVM.Guest.B1.VerifySub
