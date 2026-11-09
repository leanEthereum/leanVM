module

public import Common.Indiff.InvHash
public import Common.Fold

@[expose] public section

/-!
# Indifferentiability: the invariant holds along every run

Every step of the combined game keeps `Inv` (`inv_combStep`), the initial state satisfies it
(`inv_init`), so every reachable state of the combined game, run in the random oracle model,
satisfies it. In particular, an answer of the full view differs from the simulator's only after a
visible or a hidden collision (`diff_imp_bad_or_EC`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The initial state satisfies the invariant. -/
theorem inv_init : Inv P iv (CState.init iv : CState Dg E C Msg) ∅ := by
  refine ⟨⟨List.mem_singleton_self _, fun p hp ↦ ?_, fun p hp hne ↦ ?_, fun β hβ ↦ ?_⟩,
    fun _ _ ↦ ⟨⟨by simp [CState.init, SimState.init], by simp [CState.init, SimState.init],
      by simp [CState.init, SimState.init], by simp [CState.init, SimState.init]⟩,
      fun e ↦ ?_, rfl⟩⟩
  · simp only [CState.init, SimState.init, List.mem_singleton] at hp
    subst hp; simp [svC]
  · simp only [CState.init, SimState.init, List.mem_singleton] at hp
    subst hp; exact absurd rfl hne
  · simp [CState.init, hPaths] at hβ
  · simp only [CState.init, SimState.init, GEdge, List.not_mem_nil, false_or, false_iff]
    rintro ⟨β, B, s, v, hβ, -⟩
    simp [Hidden, CState.vis, hPaths] at hβ

/-- A coin of the combined game leaves the state and the cache alone. -/
theorem combStep_inl_run (n : ℕ) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl ((combStep P iv (.inl n)).run cs)).run c =
      (fun u ↦ (((u, u), cs), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  have h := unifFwdImpl.simulateQ_run (hashSpec := aSpec Msg Dg E C)
    (unifSpec.query n : ProbComp (Fin (n + 1))) c
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map] at h
  simp only [combStep, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_pure]
  rw [simulateQ_bind, StateT.run_bind]
  simp [h]

/-- **Every step of the combined game keeps the invariant.** -/
theorem inv_combStep (t : (dSpec Msg Dg (SpState Dg E C)).Domain) {cs : CState Dg E C Msg}
    {c : ACache Msg Dg E C} (hI : Inv P iv cs c)
    {z : ((_ × _) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combStep P iv t).run cs)).run c)) : Inv P iv z.1.2 z.2 := by
  rcases t with n | m | x | y
  · rw [combStep_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hI
  · exact inv_combHash hI m hz
  · exact inv_combFwd hI x hz
  · simp only [combStep] at hz
    obtain ⟨u, rfl⟩ := combInv_support iv y cs c hz
    exact inv_invOut u hI y

/-- The folded combined game answering with the simulator. -/
noncomputable abbrev foldIdeal : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (CState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  foldRO (combIdeal P iv)

/-- The folded combined game answering with the full view. -/
noncomputable abbrev foldReal : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (CState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  foldRO (combReal P iv)

/-- The steps of either answer of the combined game reach the states of the combined step. -/
theorem mem_support_fold_comb (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : CState Dg E C Msg × ACache Msg Dg E C) {z}
    (sel : (t : (dSpec Msg Dg (SpState Dg E C)).Domain) →
      (dSpec Msg Dg (SpState Dg E C)).Range t × (dSpec Msg Dg (SpState Dg E C)).Range t →
        (dSpec Msg Dg (SpState Dg E C)).Range t)
    (hz : z ∈ support ((foldRO (fun t ↦ sel t <$> combStep P iv t) t).run s)) :
    ∃ w ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combStep P iv t).run s.1)).run s.2), z.2 = (w.1.2, w.2) := by
  rw [foldRO_run] at hz
  simp only [StateT.run_map, simulateQ_map, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨w', hw', rfl⟩ := hw
  exact ⟨w', hw', rfl⟩

/-- The invariant holds on every reachable state of the folded combined game, with either
answer. -/
theorem inv_fold_step (sel : (t : (dSpec Msg Dg (SpState Dg E C)).Domain) →
      (dSpec Msg Dg (SpState Dg E C)).Range t × (dSpec Msg Dg (SpState Dg E C)).Range t →
        (dSpec Msg Dg (SpState Dg E C)).Range t)
    (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : CState Dg E C Msg × ACache Msg Dg E C) (hs : Inv P iv s.1 s.2)
    {z} (hz : z ∈ support ((foldRO (fun t ↦ sel t <$> combStep P iv t) t).run s)) :
    Inv P iv z.2.1 z.2.2 := by
  obtain ⟨w, hw, hz2⟩ := mem_support_fold_comb P iv t s sel hz
  rw [hz2]
  exact inv_combStep P iv t hs hw

/-- **Answers differ only after a collision.** On every reachable state of the folded combined
game run from the initial state, a differing answer implies a visible or a hidden collision. -/
theorem diff_imp_bad_or_EC (sel : (t : (dSpec Msg Dg (SpState Dg E C)).Domain) →
      (dSpec Msg Dg (SpState Dg E C)).Range t × (dSpec Msg Dg (SpState Dg E C)).Range t →
        (dSpec Msg Dg (SpState Dg E C)).Range t) {α : Type}
    (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    {z} (hz : z ∈ support ((simulateQ (foldRO (fun t ↦ sel t <$> combStep P iv t)) oa).run
      ((CState.init iv : CState Dg E C Msg), ∅))) :
    z.2.1.diff = true → z.2.1.bad = true ∨ EC P iv z.2.1.vis z.2.2 := by
  have hI := inv_of_mem_support_run (spec' := unifSpec) _ (fun s ↦ Inv P iv s.1 s.2)
    (fun t s hs z hz ↦ inv_fold_step P iv sel t s hs hz) oa (inv_init P iv) z hz
  intro hdiff
  by_contra h
  push Not at h
  have hC := hI.2 (by simpa using h.1) h.2
  rw [hC.noDiff] at hdiff
  exact Bool.false_ne_true hdiff

end Setting

end Common
