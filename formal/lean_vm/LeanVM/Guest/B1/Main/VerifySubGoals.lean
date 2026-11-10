/-
  LeanVM.Guest.B1.Main.VerifySubGoals

  Each child's `verify_sub` call on `main`'s honest run, within its own words: `verify_sub`'s
  completeness at the child (its announced stack log and rate), its exponent table
  `exponent_tables`' and its fresh claim's slot in `main`'s children's fresh claims, moved to
  `main`'s words.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5TB
public import LeanVM.Guest.B1.Main.MainGoalsDvTB
public import LeanVM.Guest.Child.RefuseZero
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.B1.Bits.Log2Placed
public import LeanVM.Guest.B1.Whir.Split

/-!
# The children's `verify_sub` calls, bounded

`VsCompleteHyp bytecode fs cert κ T B`: `verify_sub`'s completeness at an acceptable child, its
calls' trees `T μ r` and its bound `B μ r` at the child's announced stack log `μ` and rate `r`, and
every acceptable child's announced shape an opening arm of the guest (`μ ∈ [22, 28]`,
`r ∈ [1, 4]`). B1-d's `VerifySub.verify_sub_completeBT` and `child_segments` give it on the
guest's IR.

`verifySubGoalsTB_of`: for `NodeRelation` within `Limits`, the caps agreeing and no zero challenge,
child `c`'s `verify_sub` call is complete within `B` at its announced stack log and rate
(`childShape`), by a tree of `T` (`VerifySubGoalsTB`). `childShape_bounds`: every child's
announced stack log is in `[22, 28]` and its rate in `[1, 4]`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits ChildrenOk)
open LeanVM.Guest.B1 (CompleteAtDTB Returns log2Lin)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- What `verify_sub`'s completeness asks of a child `c` under the seed `seed`: its announced stack
log at least `22`, its stream within the cap, its deferring verifier accepting without a zero
challenge (the statement's refusal and the guest's), and its openings agreeing in the caps. -/
def VsChildOk (bytecode : List K) (seed : Digest) (c : Child) : Prop :=
  (∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog) ∧
    c.proof.stream.length ≤ Coverage.childStreamCap ∧
    Limits.verifyDeferredRefusingZero bytecode seed (statementDigest seed c.statement) c.freshClaim
      c.proof = true ∧
    Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim
      c.proof = true ∧
    ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree b.1 b.2

/-- **`verify_sub`'s completeness**, its calls' trees `T μ r` and its bound `B μ r` at the child's
announced stack log `μ` and rate `r` (B1-d's `verify_sub_completeBT`), and every acceptable
child's announced shape an opening arm (B1-d's `child_segments`). -/
structure VsCompleteHyp (bytecode : List K) (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (T : ℕ → ℕ → Tree → Prop) (B : ℕ → ℕ → ℕ) : Prop where
  complete : ∀ (seed : Digest) (c : Child) (sqE outE : ℕ) (Lin : Main.Layout),
    VsChildOk bytecode seed c → (∀ q ∈ log2Lin sqE, q ∈ Lin) →
    (outE, DeferredClaim.cells c.freshClaim) ∈ Lin →
    CompleteAtDTB fs cert κ "verify_sub" Lin
      [(digestHalves (statementDigest seed c.statement)).1,
        (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
        (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)] (Returns [])
      (T (childShape bytecode c).1 (childShape bytecode c).2)
      (B (childShape bytecode c).1 (childShape bytecode c).2)
  shape : ∀ (seed : Digest) (c : Child), VsChildOk bytecode seed c →
    22 ≤ (childShape bytecode c).1 ∧ (childShape bytecode c).1 ≤ 28 ∧
      1 ≤ (childShape bytecode c).2 ∧ (childShape bytecode c).2 ≤ 4

/-- `exponent_tables`' table is `log2Lin`'s. -/
theorem etL_eq (fs : String → ℕ) (fp : ℕ) (d : MainData) :
    log2Lin (etB fs (mK0 d fs fp)) = etL d fs fp := rfl

/-- **Every child's announced shape is an opening arm of the guest**: its stack log in
`[22, 28]`, its rate in `[1, 4]`. -/
theorem childShape_bounds {T : ℕ → ℕ → Tree → Prop} {B : ℕ → ℕ → ℕ} {κ : ℕ}
    (hvs : VsCompleteHyp bytecode fs cert κ T B) (hok : ChildrenOk bytecode seed w) {ch : Child}
    (hch : ch ∈ w.children) :
    22 ≤ (childShape bytecode ch).1 ∧ (childShape bytecode ch).1 ≤ 28 ∧
      1 ≤ (childShape bytecode ch).2 ∧ (childShape bytecode ch).2 ≤ 4 :=
  hvs.shape seed ch ⟨(hok _ hch).stackLogAtLeastMinimum, (hok _ hch).streamWithinCap,
    (hok _ hch).noZeroChallenge, Limits.verifyDeferredNZ_of_childOk (hok _ hch), (hok _ hch).capsAgree⟩

/-- **Each child's `verify_sub` call on the honest run, within its own bound**: `B` at its
announced stack log and rate, by a tree of `T`, the child's candidate among `open_stacked`'s
28. -/
theorem verifySubGoalsTB_of {T : ℕ → ℕ → Tree → Prop} {B : ℕ → ℕ → ℕ}
    (hbl : bytecode.length = 2 ^ 23) (hvs : VsCompleteHyp bytecode fs cert 16 T B)
    (hr : NodeRelation bytecode seed s w) (hok : ChildrenOk bytecode seed w) :
    VerifySubGoalsTB fs cert fp seed s w
      (fun c t => ∀ hc : c < w.children.length,
        B1.Whir.candidate (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2
          < 28 ∧ T (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2 t)
      (fun c => (w.children.map fun ch =>
        B (childShape bytecode ch).1 (childShape bytecode ch).2).getD c 0) := by
  intro c hc
  have hmem := List.getElem_mem hc
  set e := etB fs (mK0 (hData seed s w) fs fp) with he
  set outE := hP fs fp seed s w 6 + 24 * c with hout
  have h := hvs.complete seed w.children[c] e outE
    (log2Lin e ++ [(outE, DeferredClaim.cells w.children[c].freshClaim)])
    ⟨(hok _ hmem).stackLogAtLeastMinimum, (hok _ hmem).streamWithinCap,
      (hok _ hmem).noZeroChallenge, Limits.verifyDeferredNZ_of_childOk (hok _ hmem), (hok _ hmem).capsAgree⟩
    (fun q hq => List.mem_append_left _ hq) (List.mem_append_right _ (List.mem_singleton_self _))
  have hB : B (childShape bytecode w.children[c]).1
      (childShape bytecode w.children[c]).2 = (w.children.map fun ch =>
        B (childShape bytecode ch).1 (childShape bytecode ch).2).getD c 0 := by
    simp [List.getD_eq_getElem?_getD, hc]
  rw [hB] at h
  have hcand := childShape_bounds hvs hok hmem
  replace h := h.mono (T' := fun t => ∀ hc : c < w.children.length,
      B1.Whir.candidate (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2
        < 28 ∧ T (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2 t)
    le_rfl fun t ht _ => ⟨by unfold B1.Whir.candidate; omega, ht⟩
  have hlen : ∀ a ∈ w.children, (DeferredClaim.cells a.freshClaim).length = 24 := fun a ha => by
    simp [DeferredClaim.cells, (kid_shapes hbl hr a ha).1, bytecodeVars]
  have e1 : (hm fs fp seed s w).et = ofK (addressOfIndex e) := gen_pow_eq_ofK _
  have e3 : (hm fs fp seed s w).a400 * gen ^ (24 * c) = ofK (addressOfIndex outE) := by
    rw [hout, ← gen_pow_eq_ofK, pow_add]; rfl
  rw [e1, e3]
  refine completeAtDTB_lin_mono (fun rd hM q hq => ?_) (fun i hi => ?_) h
  · rcases List.mem_append.mp hq with hq | hq
    · rw [etL_eq] at hq
      exact hM q (List.mem_append_right _ hq)
    · rw [List.mem_singleton] at hq
      subst hq
      have r7 := reads_hLmain fs fp seed s w hM (i := 6) (by omega)
      simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at r7
      have := B1.Main.readsAt_flatMap_of w.children hlen r7 c hc
      rw [← gen_pow_eq_ofK, pow_add]
      exact this
  · obtain ⟨q, hq, h1, h2⟩ := hi
    rcases List.mem_append.mp hq with hq | hq
    · rw [etL_eq] at hq
      exact ⟨q, List.mem_append_right _ hq, h1, h2⟩
    · rw [List.mem_singleton] at hq
      subst hq
      simp only [hlen _ hmem] at h2
      have hk : 24 * c + (i - outE) < ((hOwn seed s w).getD 6 []).length := by
        simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero]
        rw [length_flatMap_const _ _ 24 hlen]
        have : c + 1 ≤ w.children.length := hc
        omega
      have := region_buf fs fp seed s w (i := 6) (by omega) hk
      rwa [show hP fs fp seed s w 6 + (24 * c + (i - outE)) = i by omega] at this

end
end LeanVM.Guest.B1.Main
