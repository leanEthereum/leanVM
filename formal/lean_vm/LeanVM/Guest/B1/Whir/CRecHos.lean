/-
  LeanVM.Guest.B1.Whir.CRecHos

  `verify_sub_completeBTP`'s `hos` from `open_stacked` placed within its bound by a tree popping its levels' `level_queries` entries.
-/

module

public import LeanVM.Guest.B1.Whir.CRecChild
public import LeanVM.Guest.B1.VerifySub.CompleteBP
public import LeanVM.Guest.B1.VerifySub.H.WhirLen

/-!
# `hos` from `open_stacked`'s pops

* `OsPopsT`: an `open_stacked` tree pops, stream by stream, its levels' `level_queries` entries (`lvPops`) for levels `Ls` of an honest run (`HonRun`) whose query steps are theirs (`lvSteps`);
* `open_stacked_completeAtBP_Spec`: `open_stacked_completeAtB_Spec` by such a tree;
* `vs_hos_of`: from it, on segments whose query steps are the child's (`SegSteps`, `child_segments_steps`) of a child the deferring verifier accepts, the `hos` that `verify_sub_completeBTP` takes (`child_merkle_sameStreams`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL)

@[expose] public section

/-- **An `open_stacked` tree pops its levels' `level_queries` entries**, stream by stream, level 0 first, for the
levels of an honest run whose query steps are theirs. -/
def OsPopsT (μ r : ℕ) (target : E) (S : KeccakState) (root : Digest) (xs : List E) (os : List (List Opening))
    (w : Whir.WhirEnd) (rd : Reader) (t : Tree) : Prop :=
  ∃ cfg Ls, Whir.HonRun μ r target S root xs os w cfg Ls ∧
    Limits.queryStepsOf (Whir.whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, Whir.stackShape μ r)]⟩ =
      Whir.lvSteps μ 0 Ls ∧
    SameStreams (t.pops coreProgram rd)
      ((List.range (Whir.osCfgR (μ - Whir.minOpenLog) (r - 1)).levels.length).flatMap (Whir.lvPops Ls μ r))

/-- **`open_stacked_completeAtB_Spec` by a tree popping its levels' `level_queries` entries.** -/
def open_stacked_completeAtBP_Spec : Prop :=
  ∀ (μ r : ℕ), Whir.minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bnd : String → ℕ),
      Lift.RunsFit fs cert → RunsConsec cert → 11 ≤ κ → OsLeafBounds fs Bnd →
      (∀ f, fs f < 2 ^ 32) →
      ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
        (os : List (List Opening)) (w : Whir.WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        Whir.RunsWith (Whir.whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, Whir.stackShape μ r)] w s' roots' →
        Whir.NoZeroChallenge μ r target S xs os root →
        Whir.CapsAgree μ r target S xs os root →
        ∀ Lin : Main.Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) →
          CompleteAtDTBR fs cert κ (Whir.openName μ) Lin
            (Whir.rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
            (OsOut μ w) (OsPopsT μ r target S root xs os w) (osBosAt fs Bnd μ)

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_sub_completeBTP`'s `hos`**, from `open_stacked_completeAtBP_Spec`, on segments whose query steps are
the child's, of a child the deferring verifier accepts. -/
theorem vs_hos_of (hP : open_stacked_completeAtBP_Spec) {bytecode : List K} {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (hS : SegSteps S)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    {κ : ℕ} (hκ : 11 ≤ κ) (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs)
    (bs : List ℕ) (sqE : ℕ) (pv : List (List E × Main.Layout)) :
    CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out (vsPos bytecode seed c)
      (osBosAt fs W.Bnd S.μs) := by
  have h : CompleteAtDTBR fs cert κ (B1.Whir.openName S.μs) [(S.cW bs, S.xsW), (sqE, expTabAllWords)]
      (B1.Whir.rateSel S.rate :: capOf S.s7.perm ++ [S.target, (digestHalves S.root).1,
        (digestHalves S.root).2, ptr (S.cW bs), ptr sqE * gen ^ winTabAt]) (vsOsOut S.μs S.w)
      (OsPopsT S.μs S.rate S.target S.s7.perm S.root S.xsW c.proof.openings S.w) (osBosAt fs W.Bnd S.μs) :=
    hP S.μs S.rate S.hmu20 S.hmu30 S.hr1 S.hr4 fs cert κ W.Bnd hrf hcons hκ W.hleaf W.hfs
      S.s7.perm S.root S.target (ptr (S.cW bs))
      (ptr sqE * gen ^ winTabAt) S.xsW c.proof.openings S.w S.s' S.roots' S.runW S.nzW
      S.capsW _ fun _ _ hL ↦ ⟨hL _ List.mem_cons_self, winTabs_vsExp fun q hq ↦ hL q (by
        simp only [vsExpLin, List.mem_singleton] at hq
        simp [hq])⟩
  refine h.mono le_rfl fun rd t ⟨cfg, Ls, hR, hst, hss⟩ ↦ ?_
  exact hss.trans (child_merkle_sameStreams S hS hrz hR rfl hst)

end
end LeanVM.Guest.B1.VerifySub
