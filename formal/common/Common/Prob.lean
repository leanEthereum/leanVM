module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds
public import Common.Defs
public import Common.Game2

@[expose] public section

/-!
# Game-playing lemmas for stateful simulations

Three generic tools for comparing and bounding runs `(simulateQ impl oa).run s` of a computation
`oa` against stateful oracle implementations, used by the indifferentiability proof:

* **identical until bad** (`prEvent_run_le_add_bad`): two implementations over the same state
  that give every event the same probability on steps that start and end in good states, and keep
  bad states bad, give every output event probabilities within the probability of a bad final
  state. The proof is VCVio's `ProgramLogic.Relational.SimulateQ.UntilBad`, restated here for
  output events;
* **state projection in distribution** (`map_run_simulateQ_evalDistEq_of_inv`): if projecting
  the state of one implementation gives, in distribution and on states satisfying a preserved
  invariant, the steps of another, the whole runs agree in distribution after projection;
* **bad-event budget** (`prEvent_run_bad_le`): if every step from a good state of small size
  reaches a bad state with probability at most its weight times `δ`, a computation with total
  weight at most `Q` ends in a bad state with probability at most `Q · δ`.

Query weights are VCVio's generalized query bounds `IsQueryBound oa Q canQuery cost` with the
budget `ℕ`, a query `t` allowed when `w t ≤ b` and costing `w t` (`QueryCostAtMost`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

universe u

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}

theorem isWeightBound_query_bind_iff (w : ι → ℕ) (t : ι) (k : spec t → OracleComp spec α)
    (Q : ℕ) : QueryCostAtMost (liftM (spec.query t) >>= k) w Q ↔
      w t ≤ Q ∧ ∀ u, QueryCostAtMost (k u) w (Q - w t) :=
  isQueryBound_query_bind_iff t k Q _ _

/-- A larger budget is still a bound. -/
theorem QueryCostAtMost.mono {oa : OracleComp spec α} {w : ι → ℕ} {Q Q' : ℕ}
    (h : QueryCostAtMost oa w Q) (hQ : Q ≤ Q') : QueryCostAtMost oa w Q' := by
  induction oa using OracleComp.inductionOn generalizing Q Q' with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h ⊢
    exact ⟨h.1.trans hQ, fun u ↦ ih u (h.2 u) (by omega)⟩

/-- Weight bounds add along a bind. -/
theorem QueryCostAtMost.bind {β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {w : ι → ℕ} {a b : ℕ} (ha : QueryCostAtMost oa w a) (hb : ∀ x, QueryCostAtMost (ob x) w b) :
    QueryCostAtMost (oa >>= ob) w (a + b) :=
  isQueryBound_bind (· + ·)
    (fun t b₁' b₂' b h ↦ ⟨le_add_left h, le_add_right h⟩)
    (fun t b₁' b₂' b h ↦ ⟨by omega, by omega⟩) ha hb

/-- A single query is bounded by its weight. -/
theorem isWeightBound_query (w : ι → ℕ) (t : ι) :
    QueryCostAtMost (liftM (spec.query t) : OracleComp spec (spec.Range t)) w (w t) :=
  (isQueryBound_query_iff t _ _ _).mpr le_rfl

section UntilBad

variable {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} [AnswerMeasure spec']

omit [AnswerMeasure spec'] in
/-- A simulation started from a bad state ends in a bad state whenever its handler keeps bad
states bad. -/
theorem forall_mem_support_run_of_bad
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_mono : ∀ t s, bad s → ∀ z ∈ support ((impl t).run s), bad z.2)
    (oa : OracleComp spec α) {s₀ : σ} (h_bad : bad s₀) :
    ∀ z ∈ support ((simulateQ impl oa).run s₀), bad z.2 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h_bad
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    exact ih us.1 (h_mono t s₀ h_bad us hus) z hz

/-- Two simulations whose handlers agree on good-to-good steps and keep bad states bad give every
event the same probability away from a bad final state (VCVio's
`prEvent_simulateQ_run_and_not_bad_eq`). -/
theorem prEvent_run_and_not_bad_eq
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (p : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[p z ∧ ¬bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[p z ∧ ¬bad z.2] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    by_cases hb : bad s₀
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
          h.2 (forall_mem_support_run_of_bad impl₁ bad h_mono₁ _ hb z hz),
        prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
          h.2 (forall_mem_support_run_of_bad impl₂ bad h_mono₂ _ hb z hz)]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      let : MeasurableSpace (spec.Range t × σ) := ⊤
      let G : Set (spec.Range t × σ) := {us | ¬bad us.2}
      have hcont (impl : QueryImpl spec (StateT σ (OracleComp spec')))
          (h_mono : ∀ t s, bad s → ∀ z ∈ support ((impl t).run s), bad z.2)
          (us : spec.Range t × σ) :
          Pr{let z ← (simulateQ impl (k us.1)).run us.2}[p z ∧ ¬bad z.2] =
            G.indicator (fun us =>
              Pr{let z ← (simulateQ impl (k us.1)).run us.2}[p z ∧ ¬bad z.2]) us := by
        by_cases hus : bad us.2
        · rw [Set.indicator_of_notMem (by simpa [G] using hus),
            prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
              h.2 (forall_mem_support_run_of_bad impl bad h_mono _ hus z hz)]
        · rw [Set.indicator_of_mem (by simpa [G] using hus)]
      have hrestrict : 𝒟[(impl₁ t).run s₀].restrict G = 𝒟[(impl₂ t).run s₀].restrict G := by
        refine Measure.ext fun A hA => ?_
        rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
        change 𝒟[(impl₁ t).run s₀] {z | z ∈ A ∧ ¬bad z.2} =
          𝒟[(impl₂ t).run s₀] {z | z ∈ A ∧ ¬bad z.2}
        rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
        exact h_agree t s₀ hb (· ∈ A)
      rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
      calc ∫⁻ us, Pr{let z ← (simulateQ impl₁ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
            ∂𝒟[(impl₁ t).run s₀]
          = ∫⁻ us, G.indicator (fun us =>
              Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]) us
              ∂𝒟[(impl₁ t).run s₀] := by
            refine lintegral_congr fun us => ?_
            rw [hcont impl₁ h_mono₁ us]
            by_cases hus : us ∈ G
            · rw [Set.indicator_of_mem hus, Set.indicator_of_mem hus, ih us.1 us.2]
            · rw [Set.indicator_of_notMem hus, Set.indicator_of_notMem hus]
        _ = ∫⁻ us, Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
              ∂(𝒟[(impl₁ t).run s₀].restrict G) :=
            lintegral_indicator MeasurableSet.of_discrete _
        _ = ∫⁻ us, Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
              ∂(𝒟[(impl₂ t).run s₀].restrict G) := by rw [hrestrict]
        _ = ∫⁻ us, Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
              ∂𝒟[(impl₂ t).run s₀] := by
            rw [← lintegral_indicator MeasurableSet.of_discrete]
            exact lintegral_congr fun us => (hcont impl₂ h_mono₂ us).symm

/-- Two simulations identical until bad end in a bad state with the same probability. -/
theorem prEvent_run_bad_eq
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[bad z.2] := by
  have h₁ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₁ oa).run s₀)
    fun z => bad z.2
  have h₂ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₂ oa).run s₀)
    fun z => bad z.2
  have hng := prEvent_run_and_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
    (fun _ ↦ True)
  simp only [true_and] at hng
  rw [OracleComp.prEvent_true_eq_one] at h₁ h₂
  have hne : Pr{let z ← (simulateQ impl₂ oa).run s₀}[¬bad z.2] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  rw [ENNReal.eq_sub_of_add_eq (hng ▸ hne) h₁, ENNReal.eq_sub_of_add_eq hne h₂, hng]

/-- **Identical until bad, for output events.** Two simulations whose handlers agree on
good-to-good steps and keep bad states bad give every output event probabilities within the
probability that the second ends in a bad state. -/
theorem prEvent_run_le_add_bad
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (p : α → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[p z.1] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[p z.1] +
        Pr{let z ← (simulateQ impl₂ oa).run s₀}[bad z.2] := by
  have hgood := prEvent_run_and_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
    (fun z ↦ p z.1)
  calc Pr{let z ← (simulateQ impl₁ oa).run s₀}[p z.1]
      ≤ Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] +
          Pr{let z ← (simulateQ impl₁ oa).run s₀}[p z.1 ∧ ¬bad z.2] :=
        prEvent_le_prEvent_add_prEvent_and_not _ _ _
    _ = Pr{let z ← (simulateQ impl₂ oa).run s₀}[bad z.2] +
          Pr{let z ← (simulateQ impl₂ oa).run s₀}[p z.1 ∧ ¬bad z.2] := by
        rw [hgood]
        congr 1
        have h₁ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₁ oa).run s₀)
          fun z => bad z.2
        have h₂ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₂ oa).run s₀)
          fun z => bad z.2
        have hng := prEvent_run_and_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
          (fun _ ↦ True)
        simp only [true_and] at hng
        rw [OracleComp.prEvent_true_eq_one] at h₁ h₂
        have hne : Pr{let z ← (simulateQ impl₂ oa).run s₀}[¬bad z.2] ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
        rw [ENNReal.eq_sub_of_add_eq (hng ▸ hne) h₁, ENNReal.eq_sub_of_add_eq hne h₂, hng]
    _ ≤ Pr{let z ← (simulateQ impl₂ oa).run s₀}[bad z.2] +
          Pr{let z ← (simulateQ impl₂ oa).run s₀}[p z.1] := by
        gcongr
        exact prEvent_mono _ _ _ fun z hz ↦ hz.1
    _ = _ := add_comm _ _

end UntilBad

section Projection

variable {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} [AnswerMeasure spec'] {σ₁ σ₂ : Type}

/-- **State projection in distribution.** If, on states satisfying an invariant preserved by
`impl₁`, projecting the state of each `impl₁` step gives the corresponding `impl₂` step in
distribution, then the whole runs agree in distribution after projection. -/
theorem map_run_simulateQ_evalDistEq_of_inv
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl₁ t).run s), inv z.2)
    (hproj : ∀ t s, inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =ᵈ (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    calc ((impl₁ t).run s >>= fun z ↦ Prod.map id proj <$> (simulateQ impl₁ (k z.1)).run z.2)
        =ᵈ ((impl₁ t).run s >>= fun z ↦ (simulateQ impl₂ (k z.1)).run (proj z.2)) :=
          EvalDistEq.bind_congr_of_support _ fun z hz ↦ ih z.1 z.2 (hinv t s hs z hz)
      _ = ((Prod.map id proj <$> (impl₁ t).run s) >>= fun z ↦
            (simulateQ impl₂ (k z.1)).run z.2) := by
          rw [bind_map_left]; rfl
      _ =ᵈ ((impl₂ t).run (proj s) >>= fun z ↦ (simulateQ impl₂ (k z.1)).run z.2) :=
          EvalDistEq.bind_left (hproj t s hs) _

/-- Output form of `map_run_simulateQ_evalDistEq_of_inv`. -/
theorem run'_simulateQ_evalDistEq_of_inv
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl₁ t).run s), inv z.2)
    (hproj : ∀ t s, inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    (simulateQ impl₁ oa).run' s =ᵈ (simulateQ impl₂ oa).run' (proj s) := by
  have h := (map_run_simulateQ_evalDistEq_of_inv impl₁ impl₂ inv proj hinv hproj oa s hs).map
    Prod.fst
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_def] using h

omit [AnswerMeasure spec'] in
/-- Invariants preserved by every step hold on every reachable final state. -/
theorem inv_of_mem_support_run
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (inv : σ → Prop)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (oa : OracleComp spec α) {s : σ} (hs : inv s) :
    ∀ z ∈ support ((simulateQ impl oa).run s), inv z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hs
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    exact ih us.1 (hinv t s hs us hus) z hz

end Projection

section Size

variable {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}

/-- **Sizes along a run.** If every step from an invariant state raises a size by at most the
step's weight, the final size of a run of total weight at most `Q` is at most the initial size
plus `Q`. -/
theorem size_le_of_mem_support_run
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (inv : σ → Prop)
    (w : ι → ℕ) (size : σ → ℕ)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hsize : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), size z.2 ≤ size s + w t)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : QueryCostAtMost oa w Q) {s₀ : σ} (hs₀ : inv s₀) :
    ∀ z ∈ support ((simulateQ impl oa).run s₀), size z.2 ≤ size s₀ + Q := by
  induction oa using OracleComp.inductionOn generalizing Q s₀ with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at hQ
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    have h1 := hsize t s₀ hs₀ us hus
    have h2 := ih us.1 (Q - w t) (hQ.2 us.1) (hinv t s₀ hs₀ us hus) z hz
    omega

end Size

section Budget

variable {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} [AnswerMeasure spec']

/-- **The bad-event budget.** Suppose every step `t` from a good state `s` of size at most
`N - w t` (and satisfying an invariant preserved by the steps) reaches a bad state with
probability at most `w t * δ`, and a step raises the size by at most `w t`. Then a computation
of total weight at most `Q`, run from a state of size at most `N - Q`, ends in a bad state with
probability at most `[bad s₀] + Q · δ`. -/
theorem prEvent_run_bad_le
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad inv : σ → Prop)
    [DecidablePred bad] (w : ι → ℕ) (size : σ → ℕ) (N : ℕ) (δ : ℝ≥0∞)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hsize : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), size z.2 ≤ size s + w t)
    (hstep : ∀ t s, inv s → ¬bad s → size s + w t ≤ N →
      Pr{let z ← (impl t).run s}[bad z.2] ≤ w t * δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : QueryCostAtMost oa w Q) (s₀ : σ) (hs₀ : inv s₀)
    (hN : size s₀ + Q ≤ N) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤ (if bad s₀ then 1 else 0) + Q * δ := by
  induction oa using OracleComp.inductionOn generalizing Q s₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
    split_ifs <;> simp
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at hQ
    obtain ⟨hwt, hk⟩ := hQ
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    let : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete]
    have hbound : ∀ z ∈ support ((impl t).run s₀),
        Pr{let y ← (simulateQ impl (k z.1)).run z.2}[bad y.2] ≤
          (if bad z.2 then 1 else 0) + (Q - w t : ℕ) * δ := fun z hz ↦
      ih z.1 (Q - w t) (hk z.1) z.2 (hinv t s₀ hs₀ z hz)
        (by have := hsize t s₀ hs₀ z hz; omega)
    calc ∫⁻ z, Pr{let y ← (simulateQ impl (k z.1)).run z.2}[bad y.2] ∂𝒟[(impl t).run s₀]
        ≤ ∫⁻ z, ((if bad z.2 then 1 else 0) + (Q - w t : ℕ) * δ) ∂𝒟[(impl t).run s₀] := by
          apply lintegral_mono_ae
          filter_upwards [ae_evalDist_of_forall_mem_support _ hbound] with z hz using hz
      _ ≤ Pr{let z ← (impl t).run s₀}[bad z.2] + (Q - w t : ℕ) * δ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
          refine add_le_add (le_of_eq ?_)
            (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
          rw [prEvent_eq_evalDist_of_discrete, ← lintegral_indicator_one MeasurableSet.of_discrete]
          exact lintegral_congr fun z ↦ by by_cases h : bad z.2 <;> simp [h, Set.indicator]
      _ ≤ ((if bad s₀ then 1 else 0) + w t * δ) + (Q - w t : ℕ) * δ := by
          gcongr
          by_cases hb : bad s₀
          · simp only [hb, ite_true]
            exact (prEvent_le_one _).trans le_self_add
          · simp only [hb, ite_false, zero_add]
            exact hstep t s₀ hs₀ hb (by omega)
      _ = (if bad s₀ then 1 else 0) + Q * δ := by
          rw [add_assoc, ← add_mul]
          congr 2
          exact_mod_cast Nat.add_sub_cancel' hwt

end Budget

end Common
