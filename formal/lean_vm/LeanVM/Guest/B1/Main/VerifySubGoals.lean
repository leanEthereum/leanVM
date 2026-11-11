/-
  LeanVM.Guest.B1.Main.VerifySubGoals

  Each child's `verify_sub` call on `main`'s honest run, within its own words: B1-d's
  `verify_sub_completeBT` at the child (its announced stack log and rate), its exponent table
  `exponent_tables`' and its fresh claim's slot in `main`'s children's fresh claims, moved to
  `main`'s words.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5TB
public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.Main.MainGoalsDvTB
public import LeanVM.Guest.Child.RefuseZero
public import LeanVM.Guest.AcceptableChild

/-!
# The children's `verify_sub` calls, bounded

`verifySubGoalsTB_of`: for `NodeRelation` within `Limits`, the caps agreeing and no zero challenge,
child `c`'s `verify_sub` call is complete within `vsBoundAt W Bvk` at its announced stack log and
rate (`childShape`), by a node of `Budget.FlatShape` for `vsTs` (`VerifySubGoalsTB`), from
`verify_keccak`'s completeness within `Bvk` and the frame runs' certificate facts.
`childShape_bounds`: every child's announced stack log is in `[20, 32]` and its rate in `[1, 4]`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits ChildrenOk)
open LeanVM.Guest.B1 (CompleteAtDTB Returns log2Lin)
open LeanVM.Guest.B1.VerifySub (VsWords vsBoundAt vsTs VkCompleteAtB verify_sub_completeBT)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- `exponent_tables`' table is `log2Lin`'s. -/
theorem etL_eq (fs : String → ℕ) (fp : ℕ) (d : MainData) :
    log2Lin (etB fs (mK0 d fs fp)) = etL d fs fp := rfl

/-- **Every child's announced shape is an opening arm of the guest**: its stack log in
`[20, 32]`, its rate in `[1, 4]`. -/
theorem childShape_bounds (hbl : bytecode.length = 2 ^ 23)
    (hok : ChildrenOk bytecode seed w) {ch : Child}
    (hch : ch ∈ w.children) :
    20 ≤ (childShape bytecode ch).1 ∧ (childShape bytecode ch).1 ≤ 32 ∧
      1 ≤ (childShape bytecode ch).2 ∧ (childShape bytecode ch).2 ≤ 4 := by
  obtain ⟨S⟩ := VerifySub.child_segments hbl seed ch (hok _ hch).stackLogAtLeastMinimum
    (Limits.verifyDeferredNZ_of_childOk (hok _ hch)) (hok _ hch).capsAgree
  rw [childShape_of S.hann]
  exact ⟨S.hmu20, S.hmu32, S.hr1, S.hr4⟩

/-- **Each child's `verify_sub` call on the honest run, within its own bound**: `vsBoundAt W Bvk`
at its announced stack log and rate, by a node of `Budget.FlatShape` for `vsTs`, the child's
stack log among `open_stacked`'s arms, `20` to `32`. -/
theorem verifySubGoalsTB_of (hbl : bytecode.length = 2 ^ 23) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert 16 Bvk)
    (hr : NodeRelation bytecode seed s w) (hok : ChildrenOk bytecode seed w) :
    VerifySubGoalsTB fs cert fp seed s w
      (fun c t => ∀ hc : c < w.children.length,
        20 ≤ (childShape bytecode w.children[c]).1 ∧ (childShape bytecode w.children[c]).1 ≤ 32 ∧
          Budget.FlatShape coreProgram "verify_sub"
            (vsTs fs W Bvk (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2) t)
      (fun c => (w.children.map fun ch =>
        vsBoundAt W Bvk (childShape bytecode ch).1 (childShape bytecode ch).2).getD c 0) := by
  intro c hc
  have hmem := List.getElem_mem hc
  set e := etB fs (mK0 (hData seed s w) fs fp) with he
  set outE := hP fs fp seed s w 6 + 24 * c with hout
  have h := verify_sub_completeBT (fs := fs) (cert := cert) hbl hrf hcons W (by norm_num) hvk seed
    w.children[c] e outE
    (log2Lin e ++ [(outE, DeferredClaim.cells w.children[c].freshClaim)])
    (hok _ hmem).stackLogAtLeastMinimum (hok _ hmem).streamWithinCap (Limits.verifyDeferredNZ_of_childOk (hok _ hmem))
    (hok _ hmem).capsAgree
    (fun q hq => List.mem_append_left _ hq) (List.mem_append_right _ (List.mem_singleton_self _))
  have hB : vsBoundAt W Bvk (childShape bytecode w.children[c]).1
      (childShape bytecode w.children[c]).2 = (w.children.map fun ch =>
        vsBoundAt W Bvk (childShape bytecode ch).1 (childShape bytecode ch).2).getD c 0 := by
    simp [List.getD_eq_getElem?_getD, hc]
  rw [hB] at h
  have hcand := childShape_bounds hbl hok hmem
  replace h := h.mono (T' := fun t => ∀ hc : c < w.children.length,
      20 ≤ (childShape bytecode w.children[c]).1 ∧ (childShape bytecode w.children[c]).1 ≤ 32 ∧
        Budget.FlatShape coreProgram "verify_sub"
          (vsTs fs W Bvk (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2) t)
    le_rfl fun t ht _ => ⟨hcand.1, hcand.2.1, ht⟩
  have hlen : ∀ a ∈ w.children, (DeferredClaim.cells a.freshClaim).length = 24 := fun a ha => by
    simp [DeferredClaim.cells, (kid_shapes hbl hr a ha).1, bytecodeVars]
  have e1 : (hm fs fp seed s w).et = ofK (addressOfIndex e) := gen_pow_eq_ofK _
  have e3 : (hm fs fp seed s w).a400 * gen ^ (24 * c) = ofK (addressOfIndex outE) := by
    rw [hout, ← gen_pow_eq_ofK, pow_add]; rfl
  rw [e1, e3]
  refine completeAtDTB_lin_mono (fun rd hM q hq => ?_) (fun i hi => ?_) (h.lowMono (by norm_num))
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
