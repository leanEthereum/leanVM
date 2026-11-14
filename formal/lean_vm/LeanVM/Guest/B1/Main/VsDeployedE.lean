/-
  LeanVM.Guest.B1.Main.VsDeployedE

  Each child's `verify_sub` call at the deployed instance by a tree popping its hints and exact at every node, given
  `verify_sub`'s callees with computed hints exact (`verifySubGoalsTBR_deployedE`).
-/

module

public import LeanVM.Guest.Budget.ClosedP
public import LeanVM.Guest.B1.Whir.CRecHosPE

/-!
# `verify_sub` at the deployed instance, every node exact

`vs_completeRE`, `verifySubGoalsTBR_deployedE`: `vs_completeR`, `verifySubGoalsTBR_deployed` by trees also exact on
the memory, given `VsKidsExact` (`verify_sub_completeBTSE`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits ChildrenOk)
open LeanVM.Guest.B1 (CompleteAtDTBR Returns RunsConsec)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vsTsAny vkBound vsExpLin vsArgs VsWordsOs VsKidsExact)
open LeanVM.Guest.End (bytecode bytecode_length)
open LeanVM.Guest.Budget (deployedVsT)

@[expose] public section

/-- **`vs_completeR`, every node exact**, given `VsKidsExact`. -/
theorem vs_completeRE {bc : List K} (hbl : bc.length = 2 ^ 23) {fs : String → ℕ} {cert : String → V → ℕ}
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs)
    {Bvk κ : ℕ} (hκ : 16 ≤ κ) (hK : VsKidsExact fs cert κ W Bvk) (seed : Digest) (c : Child)
    (sqE outE : ℕ) (Lin : Layout) (hok : VsChildOk bc seed c) (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin)
    (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ ((20 ≤ (childShape bc c).1 ∧ (childShape bc c).1 ≤ 30 ∧
        vsTsAny fs W Bvk (childShape bc c).1 (childShape bc c).2 t) ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bc seed c).drop 4)) ∧
        t.Every (ExactAt coreProgram rd))
      (vsBoundAt W Bvk (childShape bc c).1 (childShape bc c).2) := by
  obtain ⟨S, hS⟩ := B1.VerifySub.child_segments_steps hbl seed c hok.1 hok.2.2.1 hok.2.2.2
  rw [childShape_of S.hann]
  exact (B1.VerifySub.verify_sub_completeBTSE hbl hrf hcons W hκ hK S hS hok.2.2.1 sqE outE Lin hok.2.1 hexp
    hout).mono le_rfl fun _ _ h ↦ ⟨⟨⟨S.hmu20, S.hmu30, h.1.1⟩, h.1.2⟩, h.2⟩

/-- **Each child's `verify_sub` call at the deployed instance, exact at every node**: `verifySubGoalsTBR_deployed`,
given `VsKidsExact` at `B2C.fs`. -/
theorem verifySubGoalsTBR_deployedE {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hK : VsKidsExact LeanVM.Guest.B2C.fs LeanVM.Guest.B2C.cert 16 LeanVM.Guest.Count.vsWordsOs vkBound)
    (hr : NodeRelation bytecode seed s w) (hok : ChildrenOk bytecode seed w) :
    VerifySubGoalsTBR LeanVM.Guest.B2C.fs LeanVM.Guest.B2C.cert 0 seed s w
      (fun rd c t ↦ (deployedVsT w c t ∧ SameStreams (t.pops coreProgram rd) (pvH bytecode seed w c)) ∧
        t.Every (ExactAt coreProgram rd))
      (childBv (vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound) w) := by
  intro c hc
  have hmem := List.getElem_mem hc
  set e := etB LeanVM.Guest.B2C.fs (mK0 (hData seed s w) LeanVM.Guest.B2C.fs 0) with he
  set outE := hP LeanVM.Guest.B2C.fs 0 seed s w 6 + 24 * c with hout
  have h := vs_completeRE bytecode_length LeanVM.Guest.B2C.runsFit LeanVM.Guest.B2C.runsConsec
    LeanVM.Guest.Count.vsWordsOs le_rfl hK seed w.children[c] e outE
    (vsExpLin e ++ [(outE, DeferredClaim.cells w.children[c].freshClaim)])
    ⟨(hok _ hmem).stackLogAtLeastMinimum, (hok _ hmem).streamWithinCap,
      (hok _ hmem).noZeroChallenge, (hok _ hmem).capsAgree⟩
    (fun q hq => List.mem_append_left _ hq) (List.mem_append_right _ (List.mem_singleton_self _))
  have hB : vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound (childShape bytecode w.children[c]).1
      (childShape bytecode w.children[c]).2 = childBv (vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound) w c := by
    simp [childBv, List.getD_eq_getElem?_getD, hc]
  rw [hB] at h
  replace h := h.mono (T' := fun rd t ↦ (deployedVsT w c t ∧ SameStreams (t.pops coreProgram rd)
      (pvH bytecode seed w c)) ∧ t.Every (ExactAt coreProgram rd)) le_rfl fun rd t ht ↦ ⟨⟨fun _ ↦ ⟨by
        have := ht.1.1.1; have := ht.1.1.2.1; unfold B1.Whir.minOpenLog B1.Whir.openArms; omega, ht.1.1⟩, by
      rw [pvH, List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]; exact ht.1.2⟩, ht.2⟩
  have hbc := bytecode_length
  have hlen : ∀ a ∈ w.children, (DeferredClaim.cells a.freshClaim).length = 24 := fun a ha => by
    simp [DeferredClaim.cells, (kid_shapes hbc hr a ha).1, bytecodeVars]
  have e1 : (hm LeanVM.Guest.B2C.fs 0 seed s w).et = ofK (addressOfIndex e) := gen_pow_eq_ofK _
  have e3 : (hm LeanVM.Guest.B2C.fs 0 seed s w).a400 * gen ^ (24 * c) = ofK (addressOfIndex outE) := by
    rw [hout, ← gen_pow_eq_ofK, pow_add]; rfl
  show CompleteAtDTBR _ _ _ _ _ [_, _, _, _, (hm LeanVM.Guest.B2C.fs 0 seed s w).et,
    (hm LeanVM.Guest.B2C.fs 0 seed s w).a400 * gen ^ (24 * c)] _ _ _
  rw [e1, e3]
  refine completeAtDTBR_lin_mono (fun rd hM q hq => ?_) (fun i hi => ?_) (h.lowMono (by norm_num))
  · rcases List.mem_append.mp hq with hq | hq
    · rw [etL_eq] at hq
      exact hM q (List.mem_append_right _ hq)
    · rw [List.mem_singleton] at hq
      subst hq
      have r7 := reads_hLmain LeanVM.Guest.B2C.fs 0 seed s w hM (i := 6) (by omega)
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
      have := region_buf LeanVM.Guest.B2C.fs 0 seed s w (i := 6) (by omega) hk
      rwa [show hP LeanVM.Guest.B2C.fs 0 seed s w 6 + (24 * c + (i - outE)) = i by omega] at this

end
end LeanVM.Guest.B1.Main
