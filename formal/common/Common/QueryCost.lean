module

public import Statement.RandomPermutation

@[expose] public section

/-!
# Worst-case query costs

The algebra of `QueryCostAtMost`, VCVio's generalized query bound with budget `ℕ`, a query `t`
allowed when `w t ≤ b` and costing `w t`: through a query, a bind, a map, a larger budget, a
smaller weight and a stateful simulation (`isWeightBound_run_simulateQ`).
-/

open OracleComp OracleSpec

namespace Common

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'} {σ α β : Type}

theorem isWeightBound_query_bind_iff (w : ι → ℕ) (t : ι) (k : spec t → OracleComp spec α)
    (Q : ℕ) : QueryCostAtMost (liftM (spec.query t) >>= k) w Q ↔
      w t ≤ Q ∧ ∀ u, QueryCostAtMost (k u) w (Q - w t) :=
  isQueryBound_query_bind_iff t k Q _ _

theorem isWeightBound_pure (a : α) (w : ι → ℕ) (Q : ℕ) :
    QueryCostAtMost (pure a : OracleComp spec α) w Q := trivial

/-- A larger budget is still a bound. -/
theorem QueryCostAtMost.mono {oa : OracleComp spec α} {w : ι → ℕ} {Q Q' : ℕ}
    (h : QueryCostAtMost oa w Q) (hQ : Q ≤ Q') : QueryCostAtMost oa w Q' := by
  induction oa using OracleComp.inductionOn generalizing Q Q' with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h ⊢
    exact ⟨h.1.trans hQ, fun u ↦ ih u (h.2 u) (by omega)⟩

/-- Nothing weighs nothing. -/
theorem QueryCostAtMost.zero_weight (oa : OracleComp spec α) :
    QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff]
    exact ⟨le_rfl, fun u ↦ ih u⟩

/-- **Two weights' bounds add.** -/
theorem QueryCostAtMost.add_weight {oa : OracleComp spec α} {w₁ w₂ : ι → ℕ} {a b : ℕ}
    (h₁ : QueryCostAtMost oa w₁ a) (h₂ : QueryCostAtMost oa w₂ b) :
    QueryCostAtMost oa (fun t ↦ w₁ t + w₂ t) (a + b) := by
  induction oa using OracleComp.inductionOn generalizing a b with
  | pure x => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h₁ h₂ ⊢
    exact ⟨by omega, fun u ↦ (ih u (h₁.2 u) (h₂.2 u)).mono (by omega)⟩

/-- Weight bounds add along a bind. -/
theorem QueryCostAtMost.bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {w : ι → ℕ} {a b : ℕ} (ha : QueryCostAtMost oa w a) (hb : ∀ x, QueryCostAtMost (ob x) w b) :
    QueryCostAtMost (oa >>= ob) w (a + b) :=
  isQueryBound_bind (· + ·)
    (fun t b₁' b₂' b h ↦ ⟨le_add_left h, le_add_right h⟩)
    (fun t b₁' b₂' b h ↦ ⟨by omega, by omega⟩) ha hb

/-- A single query is bounded by its weight. -/
theorem isWeightBound_query (w : ι → ℕ) (t : ι) :
    QueryCostAtMost (liftM (spec.query t) : OracleComp spec (spec.Range t)) w (w t) :=
  (isQueryBound_query_iff t _ _ _).mpr le_rfl

theorem isWeightBound_map (f : α → β) {oa : OracleComp spec α} {w : ι → ℕ} {Q : ℕ}
    (h : QueryCostAtMost oa w Q) : QueryCostAtMost (f <$> oa) w Q := by
  have := h.bind (fun a ↦ isWeightBound_pure (f a) w 0)
  rwa [Nat.add_zero, bind_pure_comp] at this

/-- A smaller weight keeps a bound. -/
theorem QueryCostAtMost.mono_weight {oa : OracleComp spec α} {w w' : ι → ℕ} {Q : ℕ}
    (h : QueryCostAtMost oa w' Q) (hw : ∀ t, w t ≤ w' t) : QueryCostAtMost oa w Q := by
  induction oa using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h ⊢
    exact ⟨(hw t).trans h.1, fun u ↦ (ih u (h.2 u)).mono (by have := hw t; omega)⟩

/-- **Weight bounds through a stateful simulation**: if every step of `impl` from every state
weighs at most the query's weight, a simulated run weighs at most the computation's bound. -/
theorem isWeightBound_run_simulateQ (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (w : ι → ℕ) (w' : ι' → ℕ) (hstep : ∀ t s, QueryCostAtMost ((impl t).run s) w' (w t))
    {oa : OracleComp spec α} {Q : ℕ} (h : QueryCostAtMost oa w Q) (s : σ) :
    QueryCostAtMost ((simulateQ impl oa).run s) w' Q := by
  induction oa using OracleComp.inductionOn generalizing Q s with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact ((hstep t s).bind fun z ↦ ih z.1 (h.2 z.1) z.2).mono (by omega)

/-- **Coins weigh nothing**: a lifted coin computation weighs nothing when coins do. -/
theorem isWeightBound_liftM_probComp {hs : OracleSpec.{0, 0} ι}
    (w : (unifSpec + hs).Domain → ℕ) (hw : ∀ n, w (.inl n) = 0) (p : ProbComp α) :
    QueryCostAtMost (liftM p : OracleComp (unifSpec + hs) α) w 0 := by
  change QueryCostAtMost (OracleComp.liftComp p (unifSpec + hs)) w 0
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind n k ih =>
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change QueryCostAtMost (liftM ((unifSpec + hs).query (.inl n)) >>= fun u ↦
      OracleComp.liftComp (k u) (unifSpec + hs)) w 0
    exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨(hw n).le, fun u ↦ by
      rw [hw n]; exact ih u⟩

end Common
