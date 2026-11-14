/-
  LeanVM.Guest.Budget.ClosedP

  `main` within the deployed budget with its tree's pops (`MainCompleteP`), every family's pops instantiated:
  each child's `verify_sub` popping its hints past the advised sizes (`verify_sub_completeBTS`), its claim lists'
  digests their slots' pushes.
-/

module

public import LeanVM.Guest.Budget.Closed
public import LeanVM.Guest.B1.Whir.CRecHosP
public import LeanVM.Guest.B1.Main.L5RPops
public import LeanVM.Guest.B1.Main.MainPopsSR
public import LeanVM.Guest.B1.Main.MainGoalsClR
public import LeanVM.Guest.B1.Main.MainGoalsHClTBP

/-!
# `main` within the deployed budget, with its pops

* `completeAtDTBR_lin_mono`: `completeAtDTB_lin_mono` by a predicate of the memory;
* `vs_completeR`: `verify_sub` on a child `VsChildOk` holds of, at its announced stack log and rate, by a tree popping
  its hints past the advised sizes, stream by stream (`child_segments_steps`, `verify_sub_completeBTS`);
* `verifySubGoalsTBR_deployed`: so for each child at the deployed instance (`VerifySubGoalsTBR`, `pvH`);
* `mainPopsD`: `main`'s callees' honest entries; `ChildListPopsHyp`, `childListPopsHyp`: each child's claim lists'
  digests popping their slots' pushes; `mainCompleteP_deployed`: `MainCompleteP` within the deployed budget.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits ChildrenOk)
open LeanVM.Guest.B1 (CompleteAtDTBR Returns RunsConsec)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vsTsAny vkBound vsExpLin vsArgs VsWordsOs VkCompleteAtBK)
open LeanVM.Guest.End (bytecode bytecode_length)
open LeanVM.Guest.Budget (deployedVsT)

@[expose] public section

/-- **`completeAtDTB_lin_mono` by a predicate of the memory.** -/
theorem completeAtDTBR_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : Layout} {args : List E} {Out : List E → Layout → Prop} {T : Reader → Tree → Prop} {B : ℕ}
    (hm : ∀ rd, MemL rd Lin' → MemL rd Lin) (hr : ∀ i, RegionL Lin i → RegionL Lin' i)
    (h : CompleteAtDTBR fs cert κ f Lin args Out T B) : CompleteAtDTBR fs cert κ f Lin' args Out T B := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hM => ?_⟩
  obtain ⟨t, ⟨hn', hv, hb, hp, ht, hlo, hdd⟩, hT⟩ := hR rd hl (by
    rw [memL_append] at hM ⊢; exact ⟨hM.1, hm rd hM.2⟩)
  exact ⟨t, ⟨hn', hv, hb, hp, ht, loadsIn_mono t _ hr hlo, hdd⟩, hT⟩

/-- **`verify_sub` on a child `VsChildOk` holds of**, at its announced stack log (in `[20, 30]`) and rate, by a tree
popping the child's hints past its advised sizes, stream by stream. -/
theorem vs_completeR {bc : List K} (hbl : bc.length = 2 ^ 23) {fs : String → ℕ} {cert : String → V → ℕ}
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs)
    {Bvk κ : ℕ} (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) (seed : Digest) (c : Child)
    (sqE outE : ℕ) (Lin : Layout) (hok : VsChildOk bc seed c) (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin)
    (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ (20 ≤ (childShape bc c).1 ∧ (childShape bc c).1 ≤ 30 ∧
        vsTsAny fs W Bvk (childShape bc c).1 (childShape bc c).2 t) ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bc seed c).drop 4))
      (vsBoundAt W Bvk (childShape bc c).1 (childShape bc c).2) := by
  obtain ⟨S, hS⟩ := B1.VerifySub.child_segments_steps hbl seed c hok.1 hok.2.2.1 hok.2.2.2
  rw [childShape_of S.hann]
  exact (B1.VerifySub.verify_sub_completeBTS hbl hrf hcons W hκ hvk S hS hok.2.2.1 sqE outE Lin hok.2.1 hexp
    hout).mono le_rfl fun _ _ h ↦ ⟨⟨S.hmu20, S.hmu30, h.1⟩, h.2⟩

/-- `verify_sub`'s honest entries for child `c`: its hints past the advised sizes. -/
def pvH (bc : List K) (seed : Digest) (w : NodeWitness) (c : ℕ) : List Pop :=
  (w.children[c]?.map fun ch => (Hints.childHints bc seed ch).drop 4).getD []

/-- **Each child's `verify_sub` call at the deployed instance**, within `vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound` at its
announced stack log and rate, by a tree of `deployedVsT` popping its hints past the advised sizes. -/
theorem verifySubGoalsTBR_deployed {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation bytecode seed s w) (hok : ChildrenOk bytecode seed w) :
    VerifySubGoalsTBR LeanVM.Guest.B2C.fs LeanVM.Guest.B2C.cert 0 seed s w
      (fun rd c t ↦ deployedVsT w c t ∧ SameStreams (t.pops coreProgram rd) (pvH bytecode seed w c))
      (childBv (vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound) w) := by
  intro c hc
  have hmem := List.getElem_mem hc
  set e := etB LeanVM.Guest.B2C.fs (mK0 (hData seed s w) LeanVM.Guest.B2C.fs 0) with he
  set outE := hP LeanVM.Guest.B2C.fs 0 seed s w 6 + 24 * c with hout
  have h := vs_completeR bytecode_length LeanVM.Guest.B2C.runsFit LeanVM.Guest.B2C.runsConsec LeanVM.Guest.Count.vsWordsOs le_rfl
    (B1.VerifySub.verify_keccak_completeAtB_fs (by omega)) seed w.children[c] e outE
    (vsExpLin e ++ [(outE, DeferredClaim.cells w.children[c].freshClaim)])
    ⟨(hok _ hmem).stackLogAtLeastMinimum, (hok _ hmem).streamWithinCap,
      (hok _ hmem).noZeroChallenge, (hok _ hmem).capsAgree⟩
    (fun q hq => List.mem_append_left _ hq) (List.mem_append_right _ (List.mem_singleton_self _))
  have hB : vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound (childShape bytecode w.children[c]).1
      (childShape bytecode w.children[c]).2 = childBv (vsBoundAt LeanVM.Guest.Count.vsWordsOs vkBound) w c := by
    simp [childBv, List.getD_eq_getElem?_getD, hc]
  rw [hB] at h
  replace h := h.mono (T' := fun rd t ↦ deployedVsT w c t ∧ SameStreams (t.pops coreProgram rd)
      (pvH bytecode seed w c)) le_rfl fun rd t ht ↦ ⟨fun _ ↦ ⟨by
        have := ht.1.1; have := ht.1.2.1; unfold B1.Whir.minOpenLog B1.Whir.openArms; omega, ht.1⟩, by
      rw [pvH, List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]; exact ht.2⟩
  have hbc := bytecode_length
  have hlen : ∀ a ∈ w.children, (DeferredClaim.cells a.freshClaim).length = 24 := fun a ha => by
    simp [DeferredClaim.cells, (kid_shapes hbc hr a ha).1, bytecodeVars]
  have e1 : (hm LeanVM.Guest.B2C.fs 0 seed s w).et = ofK (addressOfIndex e) := gen_pow_eq_ofK _
  have e3 : (hm LeanVM.Guest.B2C.fs 0 seed s w).a400 * gen ^ (24 * c) = ofK (addressOfIndex outE) := by
    rw [hout, ← gen_pow_eq_ofK, pow_add]; rfl
  show CompleteAtDTBR _ _ _ _ _ [_, _, _, _, (hm LeanVM.Guest.B2C.fs 0 seed s w).et, (hm LeanVM.Guest.B2C.fs 0 seed s w).a400 * gen ^ (24 * c)]
    _ _ _
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

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (bytecode bytecode_length)
open LeanVM.Guest.B1.Main (VerifySubGoalsTBR ChildListGoalsTBR hKid hMonoX hMonoS xPlan sPlan MainPops pvH
  verifySubGoalsTBR_deployed)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **`main`'s callees' honest entries**: the claim lists', the duplicates', the raw signatures', the DA check's,
the children's (their claim lists' slots' pushes, `verify_sub`'s hints past the advised sizes), the batching's. -/
noncomputable def mainPopsD (seed : Digest) (s : NodeStatement) (w : NodeWitness) : MainPops :=
  B1.Main.mainPopsH
    (fun _ => Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2))
    (fun _ => Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2))
    (fun _ => B1.Main.l5PopsH (fun c => Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (fun c => Hints.childSlotPushes ((sPlan s w).childSlots.getD c [])) (pvH bytecode seed w) s w) s w

/-- **Each child's claim lists' digests within `ccBM`, by trees of honest shape popping their slots' pushes**, at
the deployed frame sizes. -/
def ChildListPopsHyp : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
    ChildListGoalsTBR B2C.fs B2C.cert 0 seed s w
      (fun rd c t => B1.Main.ccHonest (hKid s w c).ex (hMonoX s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (fun rd c t => B1.Main.ccHonest (hKid s w c).es (hMonoS s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((sPlan s w).childSlots.getD c []))
      (fun c => B1.Digest.ccBM B2C.fs Count.wSB (hMonoX s w c) (hKid s w c).ex)
      (fun c => B1.Digest.ccBM B2C.fs Count.wSB (hMonoS s w c) (hKid s w c).es)

/-- **`ChildListPopsHyp` holds** (`childListGoalsTBR_honest`). -/
theorem childListPopsHyp : ChildListPopsHyp := fun _ _ _ _ hl =>
  B1.Main.childListGoalsTBR_honest B2C.cert hl Count.mainStatics.ls

/-- **`main` is complete within the deployed budget with its pops**: its tree pops the honest pushes but the advised
sizes, stream by stream. -/
theorem mainCompleteP_deployed :
    MainCompleteP B2C.fs B2C.cert B2C.cnt (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  mainComplete_budgetP B2C.fs B2C.cert B2C.cnt (Pvs := deployedVsT) (Q := mainPopsD)
    (B2C.ωArm B2C.xmssArmC) B2C.jtSets Count.mainCounts (B2C.two_le_fs _)
    B1.Sig.verify_lean_xmss_complete_holds B1.Sig.sphincs_complete Count.mainStatics
    (fun _ _ _ _ hl _ => ⟨B1.Main.mainPopsS_l1 hl fun _ => rfl, B1.Main.mainPopsS_l2 hl fun _ => rfl⟩)
    (fun _ _ _ hr hl hok =>
      { clx := B1.Main.mainGoalClXR hl Count.mainStatics fun _ => rfl
        cls := B1.Main.mainGoalClSR hl Count.mainStatics fun _ => rfl
        l3 := B1.Main.mainGoalsRR_l3 hr hl Count.mainStatics.main fun _ => rfl
        l4 := B1.Main.mainGoalsRR_l4 hr hl Count.mainStatics.main fun _ => rfl
        dv := B1.Main.mainGoalsRR_dv B2C.fs B2C.cert 0 hr B2C.runsFit Count.mainStatics fun _ => rfl
        l5 := B1.Main.mainGoalsRR_l5 bytecode_length hr hl Count.mainStatics
          (verifySubGoalsTBR_deployed hr hok) (childListPopsHyp _ _ _ hr hl) fun _ => rfl
        ag := B1.Main.mainGoalsRR_ag B2C.fs B2C.cert 0 bytecode_length hr hl Count.mainStatics fun _ => rfl })
    (fun _ _ _ hr hl rd =>
      ⟨B1.Main.mainSegs_cx (fun _ => rfl) rd, B1.Main.mainSegs_cs (fun _ => rfl) rd,
        B1.Main.mainSegs_d0 (fun _ => rfl) rd, B1.Main.mainSegs_d1 (fun _ => rfl) rd,
        B1.Main.mainSegs_r2 hr hl (fun _ => rfl) rd, B1.Main.mainSegs_r3 hr hl (fun _ => rfl) rd,
        B1.Main.mainSegs_da hr (fun _ => rfl) rd, B1.Main.mainSegs_kids hl (fun _ => rfl) rd,
        B1.Main.mainSegs_agg (fun _ => rfl) rd⟩)
    (B2C.cnt_le_weight_arm B2C.xmssArmC B2C.xmssArmC_spec) l5C ccS vsCnt
    fun _ _ _ _ hl op _ _ _ _ _ hv hb hT =>
      l5_honest_weight_le op hl (fun _ hc _ _ _ _ hP hv hb => by
        obtain ⟨-, h20, h30, d, hd, hF⟩ := hP hc
        exact vs_weight_le_deployed op h20 h30 hd hF hv hb) hv hb hT

end
end LeanVM.Guest.Budget
