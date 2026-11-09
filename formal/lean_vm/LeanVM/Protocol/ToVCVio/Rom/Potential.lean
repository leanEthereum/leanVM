/-
  LeanVM.Protocol.ToVCVio.Rom.Potential

  Potential-function (supermartingale) bounds for computations run against a lazily sampled
  random oracle, VCVio's `randomOracle` among them. Candidate for VCVio.
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityNotation
import ToMathlib.Probability.UniformOn

/-!
# Potential bounds for lazily sampled random oracles

A computation `oa : OracleComp spec α` runs against a lazy random oracle: a state machine whose
state records the answers given so far. A query at a point the state already answers returns
that answer and leaves the state alone; a query at a fresh point draws a uniform answer and
records it. VCVio's `spec.randomOracle`, over the unordered `spec.QueryCache`, is one such
machine; `Rom.loggedRO` (in `LeanVM.Protocol.ToVCVio.Rom.LoggedOracle`), over the ordered
list of fresh queries, is another. `IsLazySampler lookup record impl` says that `impl` is a lazy
sampler with state lookup `lookup` and recording step `record`.

This module bounds what a computation with a total query bound can achieve against a lazy
sampler through a *potential*, a function `Φ` on states that measures how close a state is to a
bad event. The hypothesis is local, one fresh query at a time: from every state `s` and every
point `t` that `s` does not answer, the expected potential after recording a uniform answer at
`t` exceeds `Φ s` by at most `δ` (`LazyFreshStepBound lookup record Φ δ`):

  `(∑ u, Φ (record s t u)) / |R t| ≤ Φ s + δ`.

The conclusion is global (`lintegral_run_le_of_freshStepBound`): after a run of a computation
with at most `Q` queries from the state `s₀`, the expected potential of the final state is at
most `Φ s₀ + Q · δ`. By Markov's inequality at one, an event on the output and final state that
forces `1 ≤ Φ` has probability at most `Φ s₀ + Q · δ` (`prEvent_run_le_of_freshStepBound`). The
process `Φ (state after j queries) - j · δ` is a supermartingale; the lemma is the
supermartingale form of a union bound over fresh random-oracle queries. Cache hits leave the
state, and so the potential, unchanged; they spend query budget all the same, which only
loosens the bound.

The constant-increment form does not cover every argument: the birthday bound pays `k / |R|` at
the query that meets a cache with `k` entries. The budgeted form `IsLazyBudgetedPotential`
indexes the potential by the number of queries still allowed, `Φ n s`, and asks that a fresh
query take `Φ (n + 1)` down to `Φ n` in expectation and that more budget never lowers the
potential. The final bound is then `Φ Q s₀` (`lintegral_run_le_of_budgeted`). Two instances
are provided: the constant form `Φ n s = Φ s + n · δ` (`IsLazyBudgetedPotential.ofFreshStep`),
and the size-capped form (`IsLazyBudgetedPotential.ofFreshStepBelow`), where the step bound is
needed only at states of size below a cap `N`, for a size that a fresh query raises by at most
one, such as the length of a log. The capped form serves an increment `δ` that holds only while
the state is small, such as a failure probability proportional to the log length.

Potentials need not be indicator functions. A potential may be a conditional probability: the
probability, given the current state, that the remaining fresh queries complete a bad pattern.
This covers multi-query challenge derivation, where a bad challenge needs several fresh answers
to line up, and proof-of-work grinding, where the potential is the chance that a pending query
lands in the accepted set.

Leaf conditions are required on reachable outcomes only (`support`), so a bad event that is bad
only when a verifier accepts can use what acceptance says about the final state. Sequencing
(`run_simulateQ_bind`) runs the second stage from the first stage's final state, and the query
bounds of the two stages add. Two lazy samplers whose states correspond through a map `f` that
preserves lookups and recordings produce the same outcome distribution up to `f`
(`map_run_simulateQ_eq_of_isLazySampler`); this is how a bound proved over ordered logs transfers
to VCVio's `randomOracle`.

For VCVio's `randomOracle` the module specialises the bounds to caches (`FreshStepBound`,
`IsBudgetedPotential`, `prEvent_run_randomOracle_le_of_freshStepBound`) and states the
adversary-then-verifier experiment `romExperiment`: an adversary and then a verifier on the
adversary's output run against one shared oracle from the empty cache, and
`prEvent_romExperiment_le` bounds the probability that the verifier accepts while a bad
condition holds by `(Q_A + Q_V) · δ`.

Expectations are Lebesgue integrals against VCVio's output measure `𝒟[·]`; the expectation
statements take a measurable-space instance on the outcome type together with
`DiscreteMeasurableSpace`, as VCVio's own random-oracle bounds do, and the probability
statements need none.
-/

namespace LeanVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

namespace Rom

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
  [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)]

/-! ## Lazy samplers and potentials -/

section Lazy

variable {σ : Type}

/-- `impl` is a lazy random oracle over the state `σ`: at a point `t` that the state `s` answers
(`lookup s t = some u`) it returns `u` and keeps `s`; at a fresh point it draws a uniform answer
`u` and moves to `record s t u`. -/
def IsLazySampler (lookup : σ → (t : spec.Domain) → Option (spec.Range t))
    (record : σ → (t : spec.Domain) → spec.Range t → σ)
    (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∀ (t : spec.Domain) (s : σ), (impl t).run s =
    match lookup s t with
    | some u => pure (u, s)
    | none => ($ᵗ spec.Range t) >>= fun u ↦ pure (u, record s t u)

/-- `Φ` rises by at most `δ` in expectation at every fresh query: from every state `s` and
point `t` with `lookup s t = none`, the average of `Φ` over the states that record a uniform
answer at `t` is at most `Φ s + δ`. -/
def LazyFreshStepBound (lookup : σ → (t : spec.Domain) → Option (spec.Range t))
    (record : σ → (t : spec.Domain) → spec.Range t → σ) (Φ : σ → ℝ≥0∞) (δ : ℝ≥0∞) : Prop :=
  ∀ (s : σ) (t : spec.Domain), lookup s t = none →
    (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δ

/-- A potential indexed by the remaining query budget: `Φ n s` bounds what `n` more queries can
achieve from the state `s`. A fresh query lowers the budget by one and does not raise the
potential in expectation, and a larger budget never lowers it. -/
structure IsLazyBudgetedPotential (lookup : σ → (t : spec.Domain) → Option (spec.Range t))
    (record : σ → (t : spec.Domain) → spec.Range t → σ) (Φ : ℕ → σ → ℝ≥0∞) : Prop where
  /-- A fresh query is a supermartingale step from budget `n + 1` to budget `n`. -/
  fresh : ∀ (n : ℕ) (s : σ) (t : spec.Domain), lookup s t = none →
    (∑ u, Φ n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ (n + 1) s
  /-- More budget never lowers the potential; this pays for cache hits. -/
  mono : ∀ (n : ℕ) (s : σ), Φ n s ≤ Φ (n + 1) s

variable {lookup : σ → (t : spec.Domain) → Option (spec.Range t)}
  {record : σ → (t : spec.Domain) → spec.Range t → σ}

/-- Averaging `Φ + c` over a finite nonempty range adds `c` to the average of `Φ`. -/
theorem sum_add_const_div_card (t : spec.Domain) (f : spec.Range t → ℝ≥0∞) (c : ℝ≥0∞) :
    (∑ u, (f u + c)) / Fintype.card (spec.Range t) =
      (∑ u, f u) / Fintype.card (spec.Range t) + c := by
  have hcard : (Fintype.card (spec.Range t) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← (ENNReal.eq_div_iff hcard (ENNReal.natCast_ne_top _)).mpr rfl]

/-- A constant-increment potential is a budgeted potential with `δ` added per unit of budget. -/
theorem IsLazyBudgetedPotential.ofFreshStep {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞}
    (h : LazyFreshStepBound lookup record Φ δ) :
    IsLazyBudgetedPotential lookup record (fun n s ↦ Φ s + n * δ) where
  fresh n s t hs := by
    rw [sum_add_const_div_card]
    calc (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + n * δ
        ≤ Φ s + δ + n * δ := by gcongr; exact h s t hs
      _ = Φ s + ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
        rw [add_assoc, Nat.cast_succ, add_one_mul, add_comm δ]
  mono n s := by gcongr; exact_mod_cast Nat.le_succ n

/-- **The size-capped potential.** For a state size that a fresh query raises by at most one,
a step bound needed only at states of size below `N` gives a budgeted potential: `Φ s + n · δ`
while `size s + n ≤ N`, and `⊤` beyond. -/
theorem IsLazyBudgetedPotential.ofFreshStepBelow {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞}
    (size : σ → ℕ) (N : ℕ)
    (hsize : ∀ s t u, lookup s t = none → size (record s t u) ≤ size s + 1)
    (h : ∀ (s : σ) (t : spec.Domain), size s < N → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δ) :
    IsLazyBudgetedPotential lookup record
      (fun n s ↦ if size s + n ≤ N then Φ s + n * δ else ⊤) where
  fresh n s t hs := by
    by_cases hN : size s + (n + 1) ≤ N
    · rw [ite_eq_left hN]
      calc (∑ u, (if size (record s t u) + n ≤ N then Φ (record s t u) + n * δ else ⊤))
            / Fintype.card (spec.Range t)
          = (∑ u, (Φ (record s t u) + n * δ)) / Fintype.card (spec.Range t) := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ite_eq_left ?_
            have := hsize s t u hs
            omega
        _ = (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + n * δ :=
            sum_add_const_div_card t _ _
        _ ≤ Φ s + δ + n * δ := by gcongr; exact h s t (by omega) hs
        _ = Φ s + ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
            rw [add_assoc, Nat.cast_succ, add_one_mul, add_comm δ]
    · rw [ite_eq_right hN]
      exact le_top
  mono n s := by
    by_cases hN : size s + (n + 1) ≤ N
    · rw [ite_eq_left hN, ite_eq_left (by omega)]
      gcongr
      exact_mod_cast Nat.le_succ n
    · rw [ite_eq_right hN]
      exact le_top

omit [∀ t, SampleableType (spec.Range t)] in
/-- A budgeted potential is monotone in the budget. -/
theorem IsLazyBudgetedPotential.le_of_le {Φ : ℕ → σ → ℝ≥0∞}
    (hΦ : IsLazyBudgetedPotential lookup record Φ) (s : σ) {m n : ℕ} (h : m ≤ n) :
    Φ m s ≤ Φ n s :=
  monotone_nat_of_le_succ (f := fun n ↦ Φ n s) (fun n ↦ hΦ.mono n s) h

/-! ## The expectation bound -/

/-- **The budgeted potential bound.** A computation with at most `Q` queries, run against a lazy
sampler from `s₀`, has expected payoff at most `Φ Q s₀` for every payoff `g` bounded on
reachable outcomes by the potential at budget zero of the final state. -/
theorem lintegral_run_le_of_budgeted {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) {α : Type}
    [MeasurableSpace (α × σ)] [DiscreteMeasurableSpace (α × σ)]
    {Φ : ℕ → σ → ℝ≥0∞} (hΦ : IsLazyBudgetedPotential lookup record Φ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (s₀ : σ) (g : α × σ → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ impl oa).run s₀), g z ≤ Φ 0 z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ impl oa).run s₀] ≤ Φ Q s₀ := by
  induction oa using OracleComp.inductionOn generalizing Q s₀ with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure] at hg ⊢
    rw [evalDist_pure, lintegral_dirac]
    exact (hg _ (by simp)).trans (hΦ.le_of_le s₀ (Nat.zero_le Q))
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hQ
    obtain ⟨hpos, hrest⟩ := hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hrest
    rw [simulateQ_query_bind, StateT.run_bind] at hg ⊢
    simp only [OracleQuery.input_query, monadLift_self] at hg ⊢
    change ∫⁻ z, g z ∂𝒟[(impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2] ≤ _
    change ∀ z ∈ support ((impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2), _
      at hg
    rw [himpl t s₀] at hg ⊢
    rcases hs : lookup s₀ t with _ | u
    · simp only [hs, bind_assoc, pure_bind] at hg ⊢
      let _ : MeasurableSpace (spec.Range t) := ⊤
      rw [lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
        SampleableType.evalDist_uniformSample, ProbabilityTheory.lintegral_uniformOn_univ]
      calc (∑ u, ∫⁻ z, g z ∂𝒟[(simulateQ impl (mx u)).run (record s₀ t u)])
            / Fintype.card (spec.Range t)
          ≤ (∑ u, Φ n (record s₀ t u)) / Fintype.card (spec.Range t) := by
            gcongr with u
            refine ih u n (hrest u) _ fun z hz ↦ hg z ?_
            exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_uniformSample _, hz⟩
        _ ≤ Φ (n + 1) s₀ := hΦ.fresh n s₀ t hs
    · simp only [hs, pure_bind] at hg ⊢
      exact (ih u n (hrest u) s₀ hg).trans (hΦ.mono n s₀)

/-- **The potential bound.** If `Φ` rises by at most `δ` per fresh query, a computation with at
most `Q` queries, run against a lazy sampler from `s₀`, has expected payoff at most
`Φ s₀ + Q · δ` for every payoff bounded on reachable outcomes by `Φ` of the final state. -/
theorem lintegral_run_le_of_freshStepBound {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) {α : Type}
    [MeasurableSpace (α × σ)] [DiscreteMeasurableSpace (α × σ)]
    {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LazyFreshStepBound lookup record Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (s₀ : σ) (g : α × σ → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ impl oa).run s₀), g z ≤ Φ z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ impl oa).run s₀] ≤ Φ s₀ + Q * δ :=
  lintegral_run_le_of_budgeted himpl (IsLazyBudgetedPotential.ofFreshStep hΦ) oa Q hQ s₀ g
    fun z hz ↦ by simpa using hg z hz

/-! ## Probability bounds -/

/-- **Markov at one, budgeted form.** An event on reachable outcomes that forces `1 ≤ Φ 0` of
the final state has probability at most `Φ Q s₀`. -/
theorem prEvent_run_le_of_budgeted {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) {α : Type}
    {Φ : ℕ → σ → ℝ≥0∞} (hΦ : IsLazyBudgetedPotential lookup record Φ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (s₀ : σ) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ 0 z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ Q s₀ := by
  classical
  let _ : MeasurableSpace (α × σ) := ⊤
  rw [prEvent_eq_evalDist_of_discrete _ (fun z : α × σ ↦ ev z.1 z.2),
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  refine lintegral_run_le_of_budgeted himpl hΦ oa Q hQ s₀ _ fun z hz ↦ ?_
  by_cases hz' : ev z.1 z.2
  · simpa [Set.indicator_of_mem (show z ∈ {z : α × σ | ev z.1 z.2} from hz')]
      using hev z hz hz'
  · simp [Set.indicator_of_notMem (show z ∉ {z : α × σ | ev z.1 z.2} from hz')]

/-- **Markov at one.** If `Φ` rises by at most `δ` per fresh query, an event on reachable
outcomes that forces `1 ≤ Φ` of the final state has probability at most `Φ s₀ + Q · δ` after a
run with at most `Q` queries from `s₀`. -/
theorem prEvent_run_le_of_freshStepBound {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) {α : Type}
    {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LazyFreshStepBound lookup record Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (s₀ : σ) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + Q * δ :=
  prEvent_run_le_of_budgeted himpl (IsLazyBudgetedPotential.ofFreshStep hΦ) oa Q hQ s₀ ev
    fun z hz h ↦ by simpa using hev z hz h

/-- **Markov at one, size-capped form.** For a state size that a fresh query raises by at most
one, a step bound needed only at states of size below `N` bounds an event that forces `1 ≤ Φ`
by `Φ s₀ + Q · δ`, when `size s₀ + Q ≤ N`. -/
theorem prEvent_run_le_of_freshStepBelow {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) {α : Type}
    {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞} (size : σ → ℕ) (N : ℕ)
    (hsize : ∀ s t u, lookup s t = none → size (record s t u) ≤ size s + 1)
    (hΦ : ∀ (s : σ) (t : spec.Domain), size s < N → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (s₀ : σ) (hs₀ : size s₀ + Q ≤ N) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + Q * δ := by
  have h := prEvent_run_le_of_budgeted himpl
    (IsLazyBudgetedPotential.ofFreshStepBelow size N hsize hΦ) oa Q hQ s₀ ev
    fun z hz h ↦ by
      split_ifs
      · simpa using hev z hz h
      · exact le_top
  simpa only [ite_eq_left hs₀] using h

/-! ## Sequencing and transport -/

omit [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)] in
/-- Running `oa >>= ob` against a stateful oracle runs `oa` and then `ob` on its output from the
state `oa` leaves. -/
theorem run_simulateQ_bind (impl : QueryImpl spec (StateT σ ProbComp)) {α β : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (s₀ : σ) :
    (simulateQ impl (oa >>= ob)).run s₀ =
      (simulateQ impl oa).run s₀ >>= fun p ↦ (simulateQ impl (ob p.1)).run p.2 := by
  rw [simulateQ_bind, StateT.run_bind]

omit [∀ t, Fintype (spec.Range t)] in
/-- **Transport between lazy samplers.** If a map `f` of states preserves lookups and carries
each recording at a fresh point to the corresponding recording, the two lazy samplers produce
the same outcome distribution up to `f`. -/
theorem map_run_simulateQ_eq_of_isLazySampler {σ' : Type}
    {lookup' : σ' → (t : spec.Domain) → Option (spec.Range t)}
    {record' : σ' → (t : spec.Domain) → spec.Range t → σ'}
    {impl : QueryImpl spec (StateT σ ProbComp)} {impl' : QueryImpl spec (StateT σ' ProbComp)}
    (himpl : IsLazySampler lookup record impl) (himpl' : IsLazySampler lookup' record' impl')
    (f : σ → σ') (hlookup : ∀ s t, lookup' (f s) t = lookup s t)
    (hrecord : ∀ s t u, lookup s t = none → f (record s t u) = record' (f s) t u)
    {α : Type} (oa : OracleComp spec α) (s₀ : σ) :
    (fun z ↦ (z.1, f z.2)) <$> (simulateQ impl oa).run s₀ =
      (simulateQ impl' oa).run (f s₀) := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure x => simp
  | query_bind t mx ih =>
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    change (fun z ↦ (z.1, f z.2)) <$>
        ((impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2) =
      (impl' t).run (f s₀) >>= fun p ↦ (simulateQ impl' (mx p.1)).run p.2
    rw [himpl t s₀, himpl' t (f s₀), hlookup]
    rcases hs : lookup s₀ t with _ | u
    · simp only [bind_assoc, pure_bind, map_bind, ih, hrecord s₀ t _ hs]
    · simp only [pure_bind, ih]

omit [∀ t, Fintype (spec.Range t)] in
/-- Event probabilities transfer between lazy samplers whose states correspond through `f`. -/
theorem prEvent_run_eq_of_isLazySampler {σ' : Type}
    {lookup' : σ' → (t : spec.Domain) → Option (spec.Range t)}
    {record' : σ' → (t : spec.Domain) → spec.Range t → σ'}
    {impl : QueryImpl spec (StateT σ ProbComp)} {impl' : QueryImpl spec (StateT σ' ProbComp)}
    (himpl : IsLazySampler lookup record impl) (himpl' : IsLazySampler lookup' record' impl')
    (f : σ → σ') (hlookup : ∀ s t, lookup' (f s) t = lookup s t)
    (hrecord : ∀ s t u, lookup s t = none → f (record s t u) = record' (f s) t u)
    {α : Type} (oa : OracleComp spec α) (s₀ : σ) (ev : α → σ' → Prop) :
    Pr{let z ← (simulateQ impl' oa).run (f s₀)}[ev z.1 z.2] =
      Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 (f z.2)] := by
  rw [← map_run_simulateQ_eq_of_isLazySampler himpl himpl' f hlookup hrecord oa s₀]
  simp

end Lazy

/-! ## VCVio's random oracle -/

section Cache

variable [DecidableEq ι]

omit [∀ t, Fintype (spec.Range t)] in
/-- VCVio's `randomOracle` is a lazy sampler over query caches. -/
theorem randomOracle_isLazySampler :
    IsLazySampler (fun (c : spec.QueryCache) t ↦ c t) (fun c t u ↦ c.cacheQuery t u)
      spec.randomOracle :=
  fun t c ↦ randomOracle.run_eq t c

/-- `Φ` rises by at most `δ` in expectation at every fresh random-oracle query: from every
cache `c` and point `t` with `c t = none`, the average of `Φ` over the caches that record a
uniform answer at `t` is at most `Φ c + δ`. -/
abbrev FreshStepBound (Φ : spec.QueryCache → ℝ≥0∞) (δ : ℝ≥0∞) : Prop :=
  LazyFreshStepBound (fun (c : spec.QueryCache) t ↦ c t) (fun c t u ↦ c.cacheQuery t u) Φ δ

/-- A budgeted potential on random-oracle caches (`IsLazyBudgetedPotential` for
`randomOracle`). -/
abbrev IsBudgetedPotential (Φ : ℕ → spec.QueryCache → ℝ≥0∞) : Prop :=
  IsLazyBudgetedPotential (fun (c : spec.QueryCache) t ↦ c t) (fun c t u ↦ c.cacheQuery t u) Φ

/-- **The potential bound for `randomOracle`.** If `Φ` rises by at most `δ` per fresh query, a
computation with at most `Q` queries, run against the lazy random oracle from `c₀`, has
expected payoff at most `Φ c₀ + Q · δ` for every payoff bounded on reachable outcomes by `Φ` of
the final cache; in particular the expected potential of the final cache is at most
`Φ c₀ + Q · δ`. -/
theorem lintegral_run_randomOracle_le_of_freshStepBound {α : Type}
    [MeasurableSpace (α × spec.QueryCache)] [DiscreteMeasurableSpace (α × spec.QueryCache)]
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (c₀ : spec.QueryCache) (g : α × spec.QueryCache → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ spec.randomOracle oa).run c₀), g z ≤ Φ z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ spec.randomOracle oa).run c₀] ≤ Φ c₀ + Q * δ :=
  lintegral_run_le_of_freshStepBound randomOracle_isLazySampler hΦ oa Q hQ c₀ g hg

/-- The expected potential of the final cache is at most `Φ c₀ + Q · δ`. -/
theorem lintegral_potential_run_randomOracle_le {α : Type}
    [MeasurableSpace (α × spec.QueryCache)] [DiscreteMeasurableSpace (α × spec.QueryCache)]
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) (c₀ : spec.QueryCache) :
    ∫⁻ z, Φ z.2 ∂𝒟[(simulateQ spec.randomOracle oa).run c₀] ≤ Φ c₀ + Q * δ :=
  lintegral_run_randomOracle_le_of_freshStepBound hΦ oa Q hQ c₀ (fun z ↦ Φ z.2)
    fun _ _ ↦ le_rfl

/-- **Markov at one for `randomOracle`, budgeted form.** An event on reachable outcomes that
forces `1 ≤ Φ 0` of the final cache has probability at most `Φ Q c₀`. -/
theorem prEvent_run_randomOracle_le_of_budgeted {α : Type}
    {Φ : ℕ → spec.QueryCache → ℝ≥0∞} (hΦ : IsBudgetedPotential Φ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (c₀ : spec.QueryCache) (ev : α → spec.QueryCache → Prop)
    (hev : ∀ z ∈ support ((simulateQ spec.randomOracle oa).run c₀), ev z.1 z.2 → 1 ≤ Φ 0 z.2) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c₀}[ev z.1 z.2] ≤ Φ Q c₀ :=
  prEvent_run_le_of_budgeted randomOracle_isLazySampler hΦ oa Q hQ c₀ ev hev

/-- **Markov at one for `randomOracle`.** If `Φ` rises by at most `δ` per fresh query, an event
on reachable outcomes that forces `1 ≤ Φ` of the final cache has probability at most
`Φ c₀ + Q · δ` after a run with at most `Q` queries from `c₀`. -/
theorem prEvent_run_randomOracle_le_of_freshStepBound {α : Type}
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (c₀ : spec.QueryCache) (ev : α → spec.QueryCache → Prop)
    (hev : ∀ z ∈ support ((simulateQ spec.randomOracle oa).run c₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c₀}[ev z.1 z.2] ≤ Φ c₀ + Q * δ :=
  prEvent_run_le_of_freshStepBound randomOracle_isLazySampler hΦ oa Q hQ c₀ ev hev

/-- **Sequencing for `randomOracle`.** A first stage with at most `Q₁` queries followed by a
second stage, reading the first stage's output, with at most `Q₂` queries: an event that forces
`1 ≤ Φ` of the final cache has probability at most `Φ c₀ + (Q₁ + Q₂) · δ`. -/
theorem prEvent_run_randomOracle_bind_le_of_freshStepBound {α β : Type}
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (Q₁ Q₂ : ℕ)
    (hQ₁ : IsTotalQueryBound oa Q₁) (hQ₂ : ∀ a, IsTotalQueryBound (ob a) Q₂)
    (c₀ : spec.QueryCache) (ev : β → spec.QueryCache → Prop)
    (hev : ∀ z ∈ support ((simulateQ spec.randomOracle (oa >>= ob)).run c₀),
      ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ spec.randomOracle (oa >>= ob)).run c₀}[ev z.1 z.2] ≤
      Φ c₀ + (Q₁ + Q₂ : ℕ) * δ :=
  prEvent_run_randomOracle_le_of_freshStepBound hΦ (oa >>= ob) (Q₁ + Q₂)
    (isTotalQueryBound_bind hQ₁ hQ₂) c₀ ev hev

/-! ## The adversary-then-verifier experiment -/

/-- The experiment: the adversary `A` runs against the lazy random oracle from the empty cache,
then the verifier `V` reads the adversary's output and runs against the same oracle, continuing
from the cache `A` left. The outcome is the adversary's output, the verdict, and the final
cache. -/
noncomputable def romExperiment {α : Type} (A : OracleComp spec α)
    (V : α → OracleComp spec Bool) : ProbComp ((α × Bool) × spec.QueryCache) :=
  (simulateQ spec.randomOracle (A >>= fun a ↦ (a, ·) <$> V a)).run ∅

omit [∀ t, Fintype (spec.Range t)] in
/-- The experiment is the staged run: the adversary from the empty cache, then the verifier
from the adversary's final cache. -/
theorem romExperiment_eq {α : Type} (A : OracleComp spec α) (V : α → OracleComp spec Bool) :
    romExperiment A V =
      (simulateQ spec.randomOracle A).run ∅ >>= fun p ↦
        (fun r ↦ ((p.1, r.1), r.2)) <$> (simulateQ spec.randomOracle (V p.1)).run p.2 := by
  rw [romExperiment, run_simulateQ_bind]
  refine bind_congr fun p ↦ ?_
  rw [simulateQ_map, StateT.run_map]

omit [∀ t, Fintype (spec.Range t)] in
/-- An adversary whose output is mapped by `f` is the experiment of the adversary against the
verifier composed with `f`, mapped. -/
theorem romExperiment_map {α β : Type} (f : α → β) (A : OracleComp spec α)
    (V : β → OracleComp spec Bool) :
    romExperiment (f <$> A) V =
      (fun z ↦ ((f z.1.1, z.1.2), z.2)) <$> romExperiment A (fun a ↦ V (f a)) := by
  have h : (f <$> A >>= fun b ↦ (b, ·) <$> V b) =
      (fun z : α × Bool ↦ (f z.1, z.2)) <$> (A >>= fun a ↦ (a, ·) <$> V (f a)) := by
    simp [map_bind, bind_map_left, Functor.map_map]
  rw [romExperiment, romExperiment, h, simulateQ_map, StateT.run_map]

/-- **The experiment bound.** If `Φ` vanishes on the empty cache and rises by at most `δ` per
fresh query, an adversary with at most `Q_A` queries and a verifier with at most `Q_V` queries
make the verifier accept while `bad` holds of the adversary's output and the final cache with
probability at most `(Q_A + Q_V) · δ`, provided acceptance and `bad` force `1 ≤ Φ` of the final
cache on every reachable outcome. -/
theorem prEvent_romExperiment_le {α : Type}
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ) (hΦ₀ : Φ ∅ = 0)
    (A : OracleComp spec α) (V : α → OracleComp spec Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (bad : α → spec.QueryCache → Prop)
    (hbad : ∀ z ∈ support (romExperiment A V), z.1.2 = true → bad z.1.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  have h := prEvent_run_randomOracle_bind_le_of_freshStepBound hΦ A
    (fun a ↦ (a, ·) <$> V a) Q_A Q_V hA
    (fun a ↦ (isQueryBound_map_iff (V a) _ Q_V _ _).mpr (hV a)) ∅
    (fun r c ↦ r.2 = true ∧ bad r.1 c) (fun z hz h ↦ hbad z hz h.1 h.2)
  rwa [hΦ₀, zero_add] at h

end Cache

end Rom

end
end LeanVM.Protocol
