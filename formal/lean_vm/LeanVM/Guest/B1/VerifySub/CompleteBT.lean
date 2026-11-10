/-
  LeanVM.Guest.B1.VerifySub.CompleteBT

  `verify_sub` complete within its child's bound by a node whose callees are calls of their names
  within their bounds (`Budget.FlatShape`), `open_stacked` at the child's announced shape.
-/

module

public import LeanVM.Guest.B1.VerifySub.CMatch
public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.Place.OsCandAll
public import LeanVM.Guest.ChildShape
public import LeanVM.Guest.AcceptableChild

/-!
# `verify_sub` by its callees' trees

The callees' names, bounds and predicates are `VerifySub/BoundsB`'s (`vsNames`, `vsBsAt`, `vsPs`,
`vsTs`, `vsTsAny`, `vsBoundAt`). `vs_names`: the honest child's callees are calls of
`vsNames μ r (d - 16)`, the bus depth `d`.

`verify_sub_completeBT`: on an honest child (`child_segments`), `verify_sub` is complete within
the bound at its announced stack log and rate (`childShape`), by a node of `vsTsAny`
(`completeAt_flatDepRBP` with `vs_obligations` and `vs_kidsDepBP`), given `verify_keccak`'s bounded
completeness and `open_stacked`'s honest specification (`OsHonestSpec`).
`verify_sub_completeBT_fs`: at `B2C.fs`, `verify_keccak` within `vkBound`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem vs_names {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (S.kids bs sqE) (vsNames S.μs S.rate (S.d - 16)) :=
  .cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
    (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
      (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
        (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
          .nil)))))))))))))))

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_sub` is complete on every honest child within its own bound**, by a node whose
callees are calls of their names within their bounds, at the child's announced stack log and
rate. -/
theorem verify_sub_completeBT {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) (hos : OsHonestSpec) (seed : Digest)
    (c : Child) (sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree b.1 b.2)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTB fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (vsTsAny fs W Bvk (childShape bytecode c).1 (childShape bytecode c).2)
      (vsBoundAt W Bvk (childShape bytecode c).1 (childShape bytecode c).2) := by
  obtain ⟨S⟩ := child_segments hbl seed c hmu hrz hnz hcaps
  rw [childShape_of S.hann]
  have hd := S.d_bounds hbl
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs hκ hexp hout (vs_callsMatch hbl S hexp)
  have h := completeAt_flatDepRBP (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.d) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.d)) sqE)
    (vsNames S.μs S.rate (S.d - 16)) (vsBsAt W Bvk S.μs S.rate) (vsPs W)
    (fun _ ↦ vs_names S _ sqE)
    (fun _ ↦ vs_kidsDepBP hbl S hκ hrf hcons W hvk (open_stacked_completeAtB_of hos) _ sqE)
    hkr hkm hσ
  refine h.mono ?_ fun t ht ↦ ⟨S.d - 16, by omega, ht⟩
  simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]
  omega

/-- **`verify_sub` is complete within its own bound by its callees' trees** at the deployed frame
sizes, `verify_keccak` within `vkBound`. -/
theorem verify_sub_completeBT_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs LeanVM.Guest.B2C.fs) {κ : ℕ} (hκ : 16 ≤ κ)
    (hos : OsHonestSpec) (seed : Digest) (c : Child) (sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree b.1 b.2)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTB LeanVM.Guest.B2C.fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (vsTsAny LeanVM.Guest.B2C.fs W vkBound (childShape bytecode c).1 (childShape bytecode c).2)
      (vsBoundAt W vkBound (childShape bytecode c).1 (childShape bytecode c).2) :=
  verify_sub_completeBT hbl hrf hcons W hκ (verify_keccak_completeAtB_fs (by omega)) hos seed c sqE
    outE Lin hmu hst hrz hnz hcaps hexp hout

end
end LeanVM.Guest.B1.VerifySub
