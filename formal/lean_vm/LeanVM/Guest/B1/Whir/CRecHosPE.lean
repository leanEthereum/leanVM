/-
  LeanVM.Guest.B1.Whir.CRecHosPE

  `verify_sub` complete on an honest child by a node popping its hints and exact at every node, given its four callees
  with computed hints in their subtrees exact (`VsKidsExact`).
-/

module

public import LeanVM.Guest.B1.Whir.CRecHosP
public import LeanVM.Guest.B1.VerifySub.CompleteBTE
public import LeanVM.Guest.B1.Exact.Terminal
public import LeanVM.Guest.B1.Exact.VerifyTables

/-!
# `verify_sub`, popping its hints, every node exact

`open_stacked_completeAtBPE_Spec`: `open_stacked_completeAtBP_Spec` by trees also exact; `vs_hos_ofE`, `vs_hos_of`'s
from it. `VsKidsExact`: `verify_keccak` (`VkCompleteAtBKE`) and `open_stacked` by trees exact on the memory, and
`verify_tables`' own computed hints exact at its honest valuation (`VtOwnExact`; its callees are `vt_callees_ok`, the
terminal `ChildSegs.term_kidBWE`). `verify_sub_completeBTPE`, `verify_sub_completeBTSE`:
`verify_sub_completeBTP`, `verify_sub_completeBTS` by a tree also exact (`verify_sub_completeBTGE`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`open_stacked_completeAtBP_Spec` by a tree also exact on the memory.** -/
def open_stacked_completeAtBPE_Spec : Prop :=
  ∀ (μ r : ℕ), Whir.minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bnd : String → ℕ),
      Lift.RunsFit fs cert → RunsConsec cert → 11 ≤ κ → OsLeafBounds fs Bnd →
      (∀ f, fs f < 2 ^ 32) →
      ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
        (os : List (List Opening)) (w : Whir.WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        Whir.RunsWith (Whir.whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, Whir.stackShape μ r)] w s' roots' →
        Whir.NoZeroChallenge μ r target S xs os root →
        Whir.CapsAgree μ r target S xs os root →
        ∀ Lin : Main.Layout, (∀ rd, LowDef κ rd → Main.MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) →
          CompleteAtDTBR fs cert κ (Whir.openName μ) Lin
            (Whir.rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
            (OsOut μ w) (fun rd t => OsPopsT μ r target S root xs os w rd t ∧ t.Every (ExactAt coreProgram rd))
            (osBosAt fs Bnd μ)

theorem open_stacked_completeAtBPE_Spec.toBP (h : open_stacked_completeAtBPE_Spec) :
    open_stacked_completeAtBP_Spec :=
  fun μ r h1 h2 h3 h4 fs cert κ Bnd hrf hcons hκ hleaf hfs S root target cur tabs xs os w s' roots' hrun hnz hcaps
    Lin hLin =>
  (h μ r h1 h2 h3 h4 fs cert κ Bnd hrf hcons hκ hleaf hfs S root target cur tabs xs os w s' roots' hrun hnz hcaps
    Lin hLin).mono le_rfl fun _ _ h => h.1

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_sub_completeBTPE`'s `hos`**, from `open_stacked_completeAtBPE_Spec`. -/
theorem vs_hos_ofE (hP : open_stacked_completeAtBPE_Spec) {bytecode : List K} {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (hS : SegSteps S)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    {κ : ℕ} (hκ : 11 ≤ κ) (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs)
    (bs : List ℕ) (sqE : ℕ) (pv : List (List E × Main.Layout)) :
    CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out
      (fun rd t => vsPos bytecode seed c rd t ∧ t.Every (ExactAt coreProgram rd)) (osBosAt fs W.Bnd S.μs) := by
  have h : CompleteAtDTBR fs cert κ (B1.Whir.openName S.μs) [(S.cW bs, S.xsW), (sqE, expTabAllWords)]
      (B1.Whir.rateSel S.rate :: capOf S.s7.perm ++ [S.target, (digestHalves S.root).1,
        (digestHalves S.root).2, ptr (S.cW bs), ptr sqE * gen ^ winTabAt]) (vsOsOut S.μs S.w)
      (fun rd t => OsPopsT S.μs S.rate S.target S.s7.perm S.root S.xsW c.proof.openings S.w rd t ∧
        t.Every (ExactAt coreProgram rd)) (osBosAt fs W.Bnd S.μs) :=
    hP S.μs S.rate S.hmu20 S.hmu30 S.hr1 S.hr4 fs cert κ W.Bnd hrf hcons hκ W.hleaf W.hfs
      S.s7.perm S.root S.target (ptr (S.cW bs))
      (ptr sqE * gen ^ winTabAt) S.xsW c.proof.openings S.w S.s' S.roots' S.runW S.nzW
      S.capsW _ fun _ _ hL ↦ ⟨hL _ List.mem_cons_self, winTabs_vsExp fun q hq ↦ hL q (by
        simp only [vsExpLin, List.mem_singleton] at hq
        simp [hq])⟩
  refine h.mono le_rfl fun rd t ⟨⟨cfg, Ls, hR, hst, hss⟩, hE⟩ ↦ ⟨?_, hE⟩
  exact hss.trans (child_merkle_sameStreams S hS hrz hR rfl hst)

/-- **What `verify_sub`'s exactness still needs**: `verify_keccak` within `Bvk` and `open_stacked` by trees exact on
the memory, `verify_tables`' own computed hints exact at its honest valuation. -/
structure VsKidsExact (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (W : VsWordsOs fs) (Bvk : ℕ) : Prop where
  vk : VkCompleteAtBKE fs cert κ Bvk
  vt : VtOwnExact
  os : open_stacked_completeAtBPE_Spec

/-- **`verify_sub` is complete on an honest child within its own bound by a node popping `childHints` past its
advised sizes and exact at every node**, given its `open_stacked` callee's trees popping the child's Merkle hints and
its other callees with computed hints exact. -/
theorem verify_sub_completeBTPE {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hK : VsKidsExact fs cert κ W Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin)
    (hos : ∀ bs pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out
      (fun rd t => vsPos bytecode seed c rd t ∧ t.Every (ExactAt coreProgram rd)) (osBosAt fs W.Bnd S.μs)) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ (vsTsAny fs W Bvk S.μs S.rate t ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bytecode seed c).drop 4)) ∧
        t.Every (ExactAt coreProgram rd))
      (vsBoundAt W Bvk S.μs S.rate) := by
  refine CompleteAtDTBR.monoV (verify_sub_completeBTGE hbl W hκ hK.vk S sqE outE Lin hst hexp hout
    (fun _ _ ↦ S.cp_kidBP hbl (by omega) _ _) (fun B => S.vt_kidBWPE hbl (by omega) W hK.vt B) hos (fun bs pv => S.term_kidBWE hbl (by omega) W bs sqE pv)) le_rfl
    fun rd t rets hv ⟨⟨hT, σ, bufs, ks, e, hQn, hKq⟩, hE⟩ ↦ ⟨⟨hT, ?_⟩, hE⟩
  subst e
  obtain ⟨b, outs, rfl, hB⟩ := hQn
  obtain ⟨tcp, tvt, tos, ncp, nvt, nos, hmem, himpl⟩ :=
    vs_hon_child_pops S (args := vsArgs seed c sqE outE) rfl b outs hB hst hv
  have hQ : ∀ t ∈ [tcp, tvt, tos],
      VsKidQ (vsPcp S.logMem S.hs) (vsPvt S.logMem S.rowsN S.H.n) (vsPos bytecode seed c) rd t := by
    intro t ht
    obtain ⟨hm, a, r, hvt'⟩ := hmem t ht
    exact hKq t hm ⟨a, r, hvt'⟩
  have hlay : S.layout = Tables.layoutOf bytecode S.logMem S.rowsN := S.hlayout
  refine himpl ?_ ?_ ((hQ tos (by simp)).2.2 nos)
  · rw [(hQ tcp (by simp)).1 ncp, hlay, colGroupOrder_layoutOf hbl S.logMem S.hrowsL]
    rfl
  · have hn : S.H.n < 2 ^ 64 := by
      have := S.nT_le hbl
      have e : S.H.n = S.nT := rfl
      omega
    rw [(hQ tvt (by simp)).2.1 nvt, hlay, blockGroupOrder_eq hbl S.logMem S.hrowsL, count_eq_gen (by
      show S.H.n < 2 ^ 64; exact hn)]
    rfl

/-- **`verify_sub` is complete on an honest child within its own bound by a node popping `childHints` past its
advised sizes and exact at every node**, on segments whose query steps are the child's. -/
theorem verify_sub_completeBTSE {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hK : VsKidsExact fs cert κ W Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (hS : SegSteps S)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ (vsTsAny fs W Bvk S.μs S.rate t ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bytecode seed c).drop 4)) ∧
        t.Every (ExactAt coreProgram rd))
      (vsBoundAt W Bvk S.μs S.rate) :=
  verify_sub_completeBTPE hbl W hκ hK S sqE outE Lin hst hexp hout
    fun bs pv ↦ vs_hos_ofE hK.os S hS hrz (by omega) hrf hcons W bs sqE pv

end
end LeanVM.Guest.B1.VerifySub
