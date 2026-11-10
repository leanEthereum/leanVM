/-
  LeanVM.Guest.B1.VerifySub.CompleteBT

  `verify_sub` complete within its child's bound by a node whose callees are calls of their names
  within their bounds (`Budget.FlatShape`), `open_stacked` at the child's announced shape.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteAll
public import LeanVM.Guest.B1.Terminal.KidsDepBP
public import LeanVM.Guest.ChildShape
public import LeanVM.Guest.AcceptableChild

/-!
# `verify_sub` by its callees' trees

The callees' names, bounds and predicates are `VerifySub/CompleteB`'s (`vsNames`, `vsBsAt`, `vsPs`,
`vsTs`, `vsBoundAt`). `vs_kidsDepBP`: the callees on an honest child, each within its bound by
a tree of its predicate.

`verify_sub_completeBT`: `verify_sub_completeB` within the child's own bound (its announced stack
log and rate, `childShape`), by a node of `Budget.FlatShape` for `vsTs`. `verify_sub_completeBT_fs`:
at `B2C.fs`, `verify_keccak` within `vkBound`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem vs_names {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (S.kids bs sqE) (vsNames S.μs S.rate) :=
  .cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
    (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
      (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
        (.cons (fun _ ↦ rfl) .nil))))))))))))

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsDepBP_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    ks.length = Bs.length → ks.length = Ps.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtDTB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Ps.getD j fun _ ↦ True) (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepBP fs cert κ ks Bs Ps
  | [], [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | _ :: ks, _ :: Bs, _ :: Ps, hl, hl', h =>
    ⟨h 0 (by simp), kidsDepBP_of ks Bs Ps (by simpa using hl) (by simpa using hl')
      fun j hj ↦ h (j + 1) (by simp; omega)⟩

/-- The `j`-th callee of callees within their bounds. -/
theorem kidsDepB_getD {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    ∀ (j : ℕ), j < ks.length → ∀ (pv : List (List E × Main.Layout)),
      ((ks.getD j noKid pv).taken = true →
        CompleteAtB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)
  | [], _, _, _, hj, _ => absurd hj (by simp)
  | _ :: _, [], h, _, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _, pv => h.1 pv
  | _ :: _, _ :: _, h, j + 1, hj, pv => kidsDepB_getD h.2 j (by simpa using hj) pv

/-- **`verify_sub`'s callees on an honest child, each within its bound by a tree of its predicate**,
`open_stacked` within its candidate's. -/
theorem vs_kidsDepBP {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) :
    KidsDepBP fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) (vsPs W) := by
  refine kidsDepBP_of _ _ _ (by rw [ChildSegs.kids_length]; simp [vsBsAt])
    (by rw [ChildSegs.kids_length]; simp [vsPs]) fun j hj pv ↦ ?_
  have hj13 : j < 13 := by simpa [ChildSegs.kids_length] using hj
  have hB := fun j (hj : j < 13) ↦ kidsDepB_getD (vs_kidsDepBAt hbl S hκ hrf hcons W hvk bs sqE) j
    (by rw [ChildSegs.kids_length]; exact hj)
  have hμ := S.μ_bounds hbl
  interval_cases j
  · exact ⟨fun h ↦ ((hB 0 (by norm_num) pv).1 h).toDTB, (hB 0 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 1 (by norm_num) pv).1 h).toDTB, (hB 1 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 2 (by norm_num) pv).1 h).toDTB, (hB 2 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 3 (by norm_num) pv).1 h).toDTB, (hB 3 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 4 (by norm_num) pv).1 h).toDTB, (hB 4 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 5 (by norm_num) pv).1 h).toDTB, (hB 5 (by norm_num) pv).2⟩
  · obtain ⟨hok, -, -, -⟩ := S.H_run hbl
    have hHμ : S.H.μ < 30 := by
      show S.point.length < 30
      rw [(S.runG' hbl).2.2.1]; omega
    have hn : S.H.n < 29 := by have := S.n_le hbl; omega
    have hB : fs "verify_tables" + S.H.sizes.sum + ((Tables.vtBs W.Kf W.Ksh (Tables.vtRunB fs W.K10 S.H.n)).sum +
        Tables.ifFrames fs Tables.vtPre) ≤ vtMax fs W.Kf W.Ksh W.K10 := by
      rw [S.vt_sizes_sum]
      unfold vtMax
      exact le_lmax2 (vtBnd fs W.Kf W.Ksh W.K10) hHμ hn
    exact ⟨fun _ ↦ (Tables.verify_tables_completeAtTBW' (by omega) hok (S.H_shape hbl) (S.vtB bs sqE)
      W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10 W.ωv W.Kvw W.Wss W.Kw10 W.hKvw W.hssw W.h10w).mono hB
      fun _ h ↦ h, fun h ↦ by cases h⟩
  · exact ⟨fun h ↦ ((hB 7 (by norm_num) pv).1 h).toDTB, (hB 7 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 8 (by norm_num) pv).1 h).toDTB, (hB 8 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 9 (by norm_num) pv).1 h).toDTB, (hB 9 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 10 (by norm_num) pv).1 h).toDTB, (hB 10 (by norm_num) pv).2⟩
  · exact ⟨fun h ↦ ((hB 11 (by norm_num) pv).1 h).toDTB, (hB 11 (by norm_num) pv).2⟩
  · refine ⟨fun ht ↦ term_completeBW hbl S hκ _ sqE S.w_point_length pv ht W.hEqc W.hL15 W.hCsF
      W.hrs W.ωv W.Weqc W.W15 W.Wst W.Wcs W.Wrsw W.hEqcW W.hStW W.hCsW W.h15W W.hrswW, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

/-- **`verify_sub` is complete on every honest child within its own bound**, by a node whose
callees are calls of their names within their bounds, at the child's announced stack log and
rate. -/
theorem verify_sub_completeBT {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWords fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtB fs cert κ Bvk) (seed : Digest) (c : Child)
    (sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTB fs cert κ "verify_sub" Lin
      [(digestHalves (statementDigest seed c.statement)).1,
        (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
        (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)] (Returns [])
      (Budget.FlatShape coreProgram "verify_sub"
        (vsTs fs W Bvk (childShape bytecode c).1 (childShape bytecode c).2))
      (vsBoundAt W Bvk (childShape bytecode c).1 (childShape bytecode c).2) := by
  obtain ⟨S⟩ := child_segments hbl seed c hmu hnz hcaps
  rw [childShape_of S.hann]
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs hκ hexpL hout
  have h := completeAt_flatDepRBP (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.μ) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.μ)) sqE)
    (vsNames S.μs S.rate) (vsBsAt W Bvk S.μs S.rate) (vsPs W) (fun _ ↦ vs_names S _ sqE)
    (fun fp ↦ vs_kidsDepBP hbl S hκ hrf hcons W hvk _ sqE) hkr hkm hσ
  refine h.mono ?_ fun _ ht ↦ ht
  have := (S.μ_bounds hbl).2
  simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]
  omega

/-- **`verify_sub` is complete within its own bound by its callees' trees** at the deployed frame
sizes, `verify_keccak` within `vkBound`. -/
theorem verify_sub_completeBT_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hcons : RunsConsec cert) (W : VsWords LeanVM.Guest.B2C.fs) {κ : ℕ} (hκ : 16 ≤ κ)
    (seed : Digest) (c : Child) (sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTB LeanVM.Guest.B2C.fs cert κ "verify_sub" Lin
      [(digestHalves (statementDigest seed c.statement)).1,
        (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
        (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)] (Returns [])
      (Budget.FlatShape coreProgram "verify_sub"
        (vsTs LeanVM.Guest.B2C.fs W vkBound (childShape bytecode c).1 (childShape bytecode c).2))
      (vsBoundAt W vkBound (childShape bytecode c).1 (childShape bytecode c).2) :=
  verify_sub_completeBT hbl hrf hcons W hκ (verify_keccak_completeAtB_fs κ) seed c sqE outE Lin
    hmu hst hnz hcaps hexpL hout

end
end LeanVM.Guest.B1.VerifySub
