import XmssSecurity.Proof.ExpectedQueryCount

open OracleSpec OracleComp ENNReal

namespace XmssSecurity

section Frame

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/-- The expected total of a state-dependent per-query cost along a simulated run. -/
noncomputable def expectedSimulatedCost
    (implementation : QueryImpl spec (StateT σ ProbComp))
    (cost : spec.Domain → σ → ℝ≥0∞) (computation : OracleComp spec α) (s : σ) : ℝ≥0∞ :=
  (OracleComp.recOn (motive := fun _ => σ → ℝ≥0∞) computation
    (fun _ _ => 0)
    (fun input _ continuation s =>
      cost input s + ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
        continuation r.1 r.2)) s

/-- The expectation of `f` at the final state of a simulated run. -/
noncomputable def expectedFinal
    (implementation : QueryImpl spec (StateT σ ProbComp))
    (f : σ → ℝ≥0∞) (computation : OracleComp spec α) (s : σ) : ℝ≥0∞ :=
  ∑' r, Pr{let x ← (simulateQ implementation computation).run s}[x = r] * f r.2

variable (implementation : QueryImpl spec (StateT σ ProbComp))

@[simp]
theorem expectedSimulatedCost_pure (cost : spec.Domain → σ → ℝ≥0∞) (value : α) (s : σ) :
    expectedSimulatedCost implementation cost (pure value : OracleComp spec α) s = 0 :=
  rfl

@[simp]
theorem expectedSimulatedCost_query_bind (cost : spec.Domain → σ → ℝ≥0∞)
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α) (s : σ) :
    expectedSimulatedCost implementation cost (liftM (spec.query input) >>= next) s =
      cost input s + ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
        expectedSimulatedCost implementation cost (next r.1) r.2 :=
  rfl

@[simp]
theorem expectedFinal_pure (f : σ → ℝ≥0∞) (value : α) (s : σ) :
    expectedFinal implementation f (pure value : OracleComp spec α) s = f s := by
  rw [expectedFinal, simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]

theorem expectedFinal_query_bind (f : σ → ℝ≥0∞)
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α) (s : σ) :
    expectedFinal implementation f (liftM (spec.query input) >>= next) s =
      ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
        expectedFinal implementation f (next r.1) r.2 := by
  rw [expectedFinal, simulateQ_bind, StateT.run_bind, simulateQ_query,
    OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

theorem expectedFinal_le {Inv : σ → Prop}
    (hinv : ∀ input s, Inv s → ∀ r ∈ support ((implementation input).run s), Inv r.2)
    (f : σ → ℝ≥0∞) (cost : spec.Domain → σ → ℝ≥0∞)
    (hstep : ∀ input s, Inv s →
      ∑' r, Pr{let x ← (implementation input).run s}[x = r] * f r.2 ≤ f s + cost input s)
    (computation : OracleComp spec α) (s : σ) (hs : Inv s) :
    expectedFinal implementation f computation s ≤
      f s + expectedSimulatedCost implementation cost computation s := by
  induction computation using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedFinal_query_bind, expectedSimulatedCost_query_bind]
      calc
        _ ≤ ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
              (f r.2 + expectedSimulatedCost implementation cost (next r.1) r.2) := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            by_cases hr : r ∈ support ((implementation input).run s)
            · exact mul_le_mul_right (ih r.1 r.2 (hinv input s hs r hr)) _
            · simp [(prEvent_eq_zero_of_not_mem_support _) hr]
        _ = (∑' r, Pr{let x ← (implementation input).run s}[x = r] * f r.2) +
              ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
                expectedSimulatedCost implementation cost (next r.1) r.2 := by
            simp_rw [mul_add]
            exact ENNReal.tsum_add
        _ ≤ (f s + cost input s) + ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
              expectedSimulatedCost implementation cost (next r.1) r.2 :=
            add_le_add (hstep input s hs) le_rfl
        _ = _ := add_assoc _ _ _

theorem expectedFinal_ge {Inv : σ → Prop}
    (hinv : ∀ input s, Inv s → ∀ r ∈ support ((implementation input).run s), Inv r.2)
    (f : σ → ℝ≥0∞) (cost : spec.Domain → σ → ℝ≥0∞)
    (hstep : ∀ input s, Inv s →
      f s + cost input s ≤ ∑' r, Pr{let x ← (implementation input).run s}[x = r] * f r.2)
    (computation : OracleComp spec α) (s : σ) (hs : Inv s) :
    f s + expectedSimulatedCost implementation cost computation s ≤
      expectedFinal implementation f computation s := by
  induction computation using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedFinal_query_bind, expectedSimulatedCost_query_bind]
      calc
        _ = (f s + cost input s) + ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
              expectedSimulatedCost implementation cost (next r.1) r.2 :=
            (add_assoc _ _ _).symm
        _ ≤ (∑' r, Pr{let x ← (implementation input).run s}[x = r] * f r.2) +
              ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
                expectedSimulatedCost implementation cost (next r.1) r.2 :=
            add_le_add (hstep input s hs) le_rfl
        _ = ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
              (f r.2 + expectedSimulatedCost implementation cost (next r.1) r.2) := by
            simp_rw [mul_add]
            exact ENNReal.tsum_add.symm
        _ ≤ _ := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            by_cases hr : r ∈ support ((implementation input).run s)
            · exact mul_le_mul_right (ih r.1 r.2 (hinv input s hs r hr)) _
            · simp [(prEvent_eq_zero_of_not_mem_support _) hr]

theorem expectedSimulatedCost_mono {left right : spec.Domain → σ → ℝ≥0∞}
    (hle : ∀ input s, left input s ≤ right input s)
    (computation : OracleComp spec α) (s : σ) :
    expectedSimulatedCost implementation left computation s ≤
      expectedSimulatedCost implementation right computation s := by
  induction computation using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind input next ih =>
      simp only [expectedSimulatedCost_query_bind]
      gcongr with r
      · exact hle input s
      · exact ih r.1 r.2

theorem expectedSimulatedCost_add (left right : spec.Domain → σ → ℝ≥0∞)
    (computation : OracleComp spec α) (s : σ) :
    expectedSimulatedCost implementation (fun input s => left input s + right input s)
        computation s =
      expectedSimulatedCost implementation left computation s +
        expectedSimulatedCost implementation right computation s := by
  induction computation using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind input next ih =>
      simp only [expectedSimulatedCost_query_bind, ih, mul_add]
      rw [ENNReal.tsum_add]
      ac_rfl

theorem expectedSimulatedCost_const_mul (c : ℝ≥0∞) (cost : spec.Domain → σ → ℝ≥0∞)
    (computation : OracleComp spec α) (s : σ) :
    expectedSimulatedCost implementation (fun input s => c * cost input s) computation s =
      c * expectedSimulatedCost implementation cost computation s := by
  induction computation using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind input next ih =>
      simp only [expectedSimulatedCost_query_bind, ih, mul_add]
      rw [← ENNReal.tsum_mul_left]
      congr 1
      refine tsum_congr fun r => ?_
      ac_rfl

theorem expectedSimulatedCost_indicator (predicate : spec.Domain → Prop)
    [DecidablePred predicate] (computation : OracleComp spec α) (s : σ) :
    expectedSimulatedCost implementation (fun input _ => if predicate input then 1 else 0)
        computation s =
      expectedSimulatedQueryCount implementation predicate computation s := by
  induction computation using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind input next ih =>
      simp only [expectedSimulatedCost_query_bind, expectedSimulatedQueryCount_query_bind, ih]

theorem const_mul_probEvent_le_expectedFinal (f : σ → ℝ≥0∞) (E : σ → Prop) (c : ℝ≥0∞)
    (hf : ∀ s, E s → c ≤ f s) (computation : OracleComp spec α) (s : σ) :
    c * Pr{let r ← (simulateQ implementation computation).run s}[E r.2] ≤
      expectedFinal implementation f computation s := by
  classical
  rw [OracleComp.prEvent_eq_tsum_ite, expectedFinal, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun r => ?_
  split_ifs with hr
  · rw [mul_comm]
    exact mul_le_mul_right (hf r.2 hr) _
  · simp

theorem probEvent_le_expectedFinal (f : σ → ℝ≥0∞) (E : σ → Prop)
    (hf : ∀ s, E s → 1 ≤ f s) (computation : OracleComp spec α) (s : σ) :
    Pr{let r ← (simulateQ implementation computation).run s}[E r.2] ≤
      expectedFinal implementation f computation s := by
  simpa using const_mul_probEvent_le_expectedFinal implementation f E 1 hf computation s

end Frame

end XmssSecurity
