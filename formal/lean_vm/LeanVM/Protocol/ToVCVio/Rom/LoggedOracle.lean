/-
  LeanVM.Protocol.ToVCVio.Rom.LoggedOracle

  The lazy random oracle over an ordered log of fresh queries, its potential bounds, and its
  equivalence with VCVio's `randomOracle`. Candidate for VCVio.
-/

module

public import LeanVM.Protocol.ToVCVio.Rom.Potential

/-!
# The logged lazy random oracle

`Rom.loggedRO` is the lazy random oracle for `D →ₒ R` whose state is the ordered list of the
fresh queries made so far, `ℓ : List (D × R)`. A query at `t` looks `t` up in the log, first
match first (`logLookup`); if it is absent it draws `u` uniformly from `R` and appends `(t, u)`
at the end of the log. Unlike VCVio's `QueryCache`, the log records the order of fresh queries,
so a potential on logs can tell a query that predicts a value referenced earlier from one made
in the honest order.

The bounds of `LeanVM.Protocol.ToVCVio.Rom.Potential` apply to `loggedRO`
(`loggedRO_isLazySampler`). For `Φ : List (D × R) → ℝ≥0∞` with
`(∑ u, Φ (ℓ ++ [(t, u)])) / |R| ≤ Φ ℓ + δ` for every log `ℓ` and every `t` not among the inputs
of `ℓ` (`LogFreshStepBound Φ δ`), a computation with at most `Q` queries run from `ℓ₀` has
expected final potential at most `Φ ℓ₀ + Q · δ` (`lintegral_run_loggedRO_le_of_freshStepBound`),
and an event forcing `1 ≤ Φ` of the final log has probability at most `Φ ℓ₀ + Q · δ`
(`prEvent_run_loggedRO_le_of_freshStepBound`). The length-capped form
(`prEvent_run_loggedRO_le_of_freshStepBelow`) needs the step bound only at logs shorter than a
cap `N ≥ |ℓ₀| + Q`, for an increment that grows with the log length.

The log determines a cache, its lookup function (`cacheOf`). Running `loggedRO` from `ℓ₀` and
reading the final log as a cache has the same distribution of output and cache as VCVio's
`randomOracle` run from `cacheOf ℓ₀` (`map_run_simulateQ_loggedRO`): the two oracles answer the
same points the same way and record the same fresh answers. So a bound proved with an
order-aware potential on logs is a bound about `randomOracle`
(`prEvent_romExperiment_le_of_logFreshStepBound`): the adversary-then-verifier experiment
`romExperiment` of `Potential` accepts while a bad condition of the adversary's output and the
final cache holds with probability at most `(Q_A + Q_V) · δ`, provided acceptance and the bad
condition force `1 ≤ Φ` of the final log on every reachable outcome of the logged experiment
`logExperiment`.
-/

namespace LeanVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

namespace Rom

variable {D R : Type} [DecidableEq D]

/-! ## Logs -/

/-- The answer a log gives at `t`: the output of its first entry with input `t`. -/
def logLookup : List (D × R) → D → Option R
  | [], _ => none
  | e :: ℓ, t => if e.1 = t then some e.2 else logLookup ℓ t

@[simp] theorem logLookup_nil (t : D) : logLookup ([] : List (D × R)) t = none := rfl

theorem logLookup_cons (e : D × R) (ℓ : List (D × R)) (t : D) :
    logLookup (e :: ℓ) t = if e.1 = t then some e.2 else logLookup ℓ t := rfl

/-- A log has no answer at `t` exactly when `t` is not among its inputs. -/
theorem logLookup_eq_none_iff (ℓ : List (D × R)) (t : D) :
    logLookup ℓ t = none ↔ t ∉ ℓ.map Prod.fst := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    rw [logLookup_cons]
    by_cases h : e.1 = t
    · simp [h]
    · simp [h, ih, Ne.symm h]

/-- Appending an entry at a point the log does not answer adds that one answer. -/
theorem logLookup_append_singleton (ℓ : List (D × R)) (t t' : D) (u : R)
    (h : logLookup ℓ t = none) :
    logLookup (ℓ ++ [(t, u)]) t' = if t' = t then some u else logLookup ℓ t' := by
  induction ℓ with
  | nil => simp [logLookup_cons, eq_comm]
  | cons e ℓ ih =>
    rw [logLookup_cons] at h
    by_cases he : e.1 = t
    · simp [he] at h
    · rw [ite_eq_right he] at h
      rw [List.cons_append, logLookup_cons, logLookup_cons, ih h]
      by_cases he' : e.1 = t'
      · subst he'
        simp [he]
      · simp [he']

/-- The cache a log determines: its lookup function. -/
def cacheOf (ℓ : List (D × R)) : (D →ₒ R).QueryCache :=
  QueryCache.ofFn (logLookup ℓ)

@[simp] theorem cacheOf_apply (ℓ : List (D × R)) (t : D) : cacheOf ℓ t = logLookup ℓ t := rfl

@[simp] theorem cacheOf_nil : cacheOf ([] : List (D × R)) = ∅ :=
  QueryCache.ext fun _ ↦ rfl

/-- Appending a fresh entry to a log records it in the cache. -/
theorem cacheOf_append_singleton (ℓ : List (D × R)) (t : D) (u : R)
    (h : logLookup ℓ t = none) :
    cacheOf (ℓ ++ [(t, u)]) = (cacheOf ℓ).cacheQuery t u := by
  refine QueryCache.ext fun t' ↦ ?_
  rw [cacheOf_apply, logLookup_append_singleton ℓ t t' u h]
  by_cases ht : t' = t
  · subst ht
    simp
  · simp [ht]

/-! ## The logged random oracle -/

variable [SampleableType R]

/-- The lazy random oracle over an ordered log: a point the log answers gets that answer, and a
fresh point gets a uniform answer appended at the end of the log. -/
def loggedRO : QueryImpl (D →ₒ R) (StateT (List (D × R)) ProbComp) :=
  fun t ↦ StateT.mk fun ℓ ↦
    match logLookup ℓ t with
    | some u => pure (u, ℓ)
    | none => ($ᵗ R) >>= fun u ↦ pure (u, ℓ ++ [(t, u)])

/-- `loggedRO` is a lazy sampler over logs. -/
theorem loggedRO_isLazySampler :
    IsLazySampler (fun (ℓ : List (D × R)) t ↦ logLookup ℓ t) (fun ℓ t u ↦ ℓ ++ [(t, u)])
      (loggedRO (D := D) (R := R)) := by
  intro t ℓ
  rcases h : logLookup ℓ t with _ | u <;> simp [loggedRO, h]

/-- **The bridge to `randomOracle`.** Running `loggedRO` from `ℓ₀` and reading the final log as
a cache is running VCVio's `randomOracle` from `cacheOf ℓ₀`. -/
theorem map_run_simulateQ_loggedRO {α : Type} (oa : OracleComp (D →ₒ R) α)
    (ℓ₀ : List (D × R)) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> (simulateQ loggedRO oa).run ℓ₀ =
      (simulateQ (D →ₒ R).randomOracle oa).run (cacheOf ℓ₀) :=
  map_run_simulateQ_eq_of_isLazySampler loggedRO_isLazySampler randomOracle_isLazySampler
    cacheOf (fun _ _ ↦ rfl) (fun ℓ t u h ↦ cacheOf_append_singleton ℓ t u h) oa ℓ₀

/-- The bridge from the empty log. -/
theorem map_run_simulateQ_loggedRO_nil {α : Type} (oa : OracleComp (D →ₒ R) α) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> (simulateQ loggedRO oa).run [] =
      (simulateQ (D →ₒ R).randomOracle oa).run ∅ := by
  rw [map_run_simulateQ_loggedRO, cacheOf_nil]

/-- Events of a `randomOracle` run from the empty cache are events of the `loggedRO` run from
the empty log, read through `cacheOf`. -/
theorem prEvent_run_randomOracle_eq_loggedRO {α : Type} (oa : OracleComp (D →ₒ R) α)
    (ev : α → (D →ₒ R).QueryCache → Prop) :
    Pr{let z ← (simulateQ (D →ₒ R).randomOracle oa).run ∅}[ev z.1 z.2] =
      Pr{let z ← (simulateQ loggedRO oa).run []}[ev z.1 (cacheOf z.2)] := by
  rw [← cacheOf_nil (D := D) (R := R)]
  exact prEvent_run_eq_of_isLazySampler loggedRO_isLazySampler randomOracle_isLazySampler
    cacheOf (fun _ _ ↦ rfl) (fun ℓ t u h ↦ cacheOf_append_singleton ℓ t u h) oa [] ev

/-! ## Potentials on logs -/

variable [Fintype R]

/-- `Φ` rises by at most `δ` in expectation at every fresh logged query: for every log `ℓ` and
every `t` that `ℓ` does not answer, `(∑ u, Φ (ℓ ++ [(t, u)])) / |R| ≤ Φ ℓ + δ`. -/
abbrev LogFreshStepBound (Φ : List (D × R) → ℝ≥0∞) (δ : ℝ≥0∞) : Prop :=
  LazyFreshStepBound (spec := D →ₒ R) (fun (ℓ : List (D × R)) t ↦ logLookup ℓ t)
    (fun ℓ t u ↦ ℓ ++ [(t, u)]) Φ δ

omit [SampleableType R] in
/-- The step condition in terms of the log's inputs. -/
theorem logFreshStepBound_iff (Φ : List (D × R) → ℝ≥0∞) (δ : ℝ≥0∞) :
    LogFreshStepBound Φ δ ↔ ∀ (ℓ : List (D × R)) (t : D), t ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card R ≤ Φ ℓ + δ := by
  simp only [LogFreshStepBound, LazyFreshStepBound, logLookup_eq_none_iff]

/-- **The potential bound for `loggedRO`.** If `Φ` rises by at most `δ` per fresh query, a
computation with at most `Q` queries run from the log `ℓ₀` has expected payoff at most
`Φ ℓ₀ + Q · δ` for every payoff bounded on reachable outcomes by `Φ` of the final log. -/
theorem lintegral_run_loggedRO_le_of_freshStepBound {α : Type}
    [MeasurableSpace (α × List (D × R))] [DiscreteMeasurableSpace (α × List (D × R))]
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (oa : OracleComp (D →ₒ R) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (D × R)) (g : α × List (D × R) → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ loggedRO oa).run ℓ₀), g z ≤ Φ z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ loggedRO oa).run ℓ₀] ≤ Φ ℓ₀ + Q * δ :=
  lintegral_run_le_of_freshStepBound loggedRO_isLazySampler hΦ oa Q hQ ℓ₀ g hg

/-- The expected potential of the final log is at most `Φ ℓ₀ + Q · δ`. -/
theorem lintegral_potential_run_loggedRO_le {α : Type}
    [MeasurableSpace (α × List (D × R))] [DiscreteMeasurableSpace (α × List (D × R))]
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (oa : OracleComp (D →ₒ R) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (D × R)) :
    ∫⁻ z, Φ z.2 ∂𝒟[(simulateQ loggedRO oa).run ℓ₀] ≤ Φ ℓ₀ + Q * δ :=
  lintegral_run_loggedRO_le_of_freshStepBound hΦ oa Q hQ ℓ₀ (fun z ↦ Φ z.2) fun _ _ ↦ le_rfl

/-- **Markov at one for `loggedRO`.** An event on reachable outcomes that forces `1 ≤ Φ` of the
final log has probability at most `Φ ℓ₀ + Q · δ`. -/
theorem prEvent_run_loggedRO_le_of_freshStepBound {α : Type}
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (oa : OracleComp (D →ₒ R) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (D × R)) (ev : α → List (D × R) → Prop)
    (hev : ∀ z ∈ support ((simulateQ loggedRO oa).run ℓ₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ loggedRO oa).run ℓ₀}[ev z.1 z.2] ≤ Φ ℓ₀ + Q * δ :=
  prEvent_run_le_of_freshStepBound loggedRO_isLazySampler hΦ oa Q hQ ℓ₀ ev hev

/-- **Markov at one for `loggedRO`, length-capped form.** A step bound needed only at logs
shorter than `N` bounds an event forcing `1 ≤ Φ` by `Φ ℓ₀ + Q · δ`, when `|ℓ₀| + Q ≤ N`. -/
theorem prEvent_run_loggedRO_le_of_freshStepBelow {α : Type}
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ)
    (hΦ : ∀ (ℓ : List (D × R)) (t : D), ℓ.length < N → t ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card R ≤ Φ ℓ + δ)
    (oa : OracleComp (D →ₒ R) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (D × R)) (hℓ₀ : ℓ₀.length + Q ≤ N) (ev : α → List (D × R) → Prop)
    (hev : ∀ z ∈ support ((simulateQ loggedRO oa).run ℓ₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ loggedRO oa).run ℓ₀}[ev z.1 z.2] ≤ Φ ℓ₀ + Q * δ :=
  prEvent_run_le_of_freshStepBelow loggedRO_isLazySampler List.length N
    (fun ℓ t u _ ↦ by simp) (fun ℓ t hN h ↦ hΦ ℓ t hN ((logLookup_eq_none_iff ℓ t).mp h))
    oa Q hQ ℓ₀ hℓ₀ ev hev

/-! ## The logged experiment -/

/-- The adversary-then-verifier experiment over the log: the adversary `A` runs against
`loggedRO` from the empty log, then the verifier `V` on the adversary's output continues with
the same log. The outcome is the adversary's output, the verdict, and the final log. -/
noncomputable def logExperiment {α : Type} (A : OracleComp (D →ₒ R) α)
    (V : α → OracleComp (D →ₒ R) Bool) : ProbComp ((α × Bool) × List (D × R)) :=
  (simulateQ loggedRO (A >>= fun a ↦ (a, ·) <$> V a)).run []

omit [Fintype R] in
/-- The experiment over `randomOracle` is the logged experiment read through `cacheOf`. -/
theorem map_logExperiment {α : Type} (A : OracleComp (D →ₒ R) α)
    (V : α → OracleComp (D →ₒ R) Bool) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> logExperiment A V = romExperiment A V :=
  map_run_simulateQ_loggedRO_nil _

omit [Fintype R] in
/-- Events of the `randomOracle` experiment are events of the logged experiment read through
`cacheOf`. -/
theorem prEvent_romExperiment_eq_logExperiment {α : Type} (A : OracleComp (D →ₒ R) α)
    (V : α → OracleComp (D →ₒ R) Bool) (ev : (α × Bool) → (D →ₒ R).QueryCache → Prop) :
    Pr{let z ← romExperiment A V}[ev z.1 z.2] =
      Pr{let z ← logExperiment A V}[ev z.1 (cacheOf z.2)] :=
  prEvent_run_randomOracle_eq_loggedRO _ ev

/-- **The logged experiment bound.** If `Φ` vanishes on the empty log and rises by at most `δ`
per fresh query, an adversary with at most `Q_A` queries and a verifier with at most `Q_V`
queries make the verifier accept while `bad` holds with probability at most `(Q_A + Q_V) · δ`,
provided acceptance and `bad` force `1 ≤ Φ` of the final log on every reachable outcome. -/
theorem prEvent_logExperiment_le {α : Type}
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ) (hΦ₀ : Φ [] = 0)
    (A : OracleComp (D →ₒ R) α) (V : α → OracleComp (D →ₒ R) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (bad : α → List (D × R) → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← logExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  have h := prEvent_run_loggedRO_le_of_freshStepBound hΦ _ (Q_A + Q_V)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (V a) _ Q_V _ _).mpr (hV a)) []
    (fun r ℓ ↦ r.2 = true ∧ bad r.1 ℓ) (fun z hz h ↦ hbad z hz h.1 h.2)
  rwa [hΦ₀, zero_add] at h

/-- **The logged experiment bound, length-capped form.** As `prEvent_logExperiment_le`, with the
step bound needed only at logs shorter than `N ≥ Q_A + Q_V`. -/
theorem prEvent_logExperiment_le_of_freshStepBelow {α : Type}
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ)
    (hΦ : ∀ (ℓ : List (D × R)) (t : D), ℓ.length < N → t ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card R ≤ Φ ℓ + δ) (hΦ₀ : Φ [] = 0)
    (A : OracleComp (D →ₒ R) α) (V : α → OracleComp (D →ₒ R) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (hN : Q_A + Q_V ≤ N) (bad : α → List (D × R) → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← logExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  have h := prEvent_run_loggedRO_le_of_freshStepBelow N hΦ _ (Q_A + Q_V)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (V a) _ Q_V _ _).mpr (hV a)) []
    (by simpa using hN) (fun r ℓ ↦ r.2 = true ∧ bad r.1 ℓ) (fun z hz h ↦ hbad z hz h.1 h.2)
  rwa [hΦ₀, zero_add] at h

/-- **The `randomOracle` experiment bound through an order-aware potential.** If `Φ` on logs
vanishes on the empty log and rises by at most `δ` per fresh query at logs shorter than
`N ≥ Q_A + Q_V`, then in VCVio's `romExperiment` an adversary with at most `Q_A` queries and a
verifier with at most `Q_V` queries make the verifier accept while `bad` holds of the
adversary's output and the final cache with probability at most `(Q_A + Q_V) · δ`, provided
that on every reachable outcome of the logged experiment, acceptance and `bad` of the log's
cache force `1 ≤ Φ` of the final log. -/
theorem prEvent_romExperiment_le_of_logFreshStepBelow {α : Type}
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ)
    (hΦ : ∀ (ℓ : List (D × R)) (t : D), ℓ.length < N → t ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card R ≤ Φ ℓ + δ) (hΦ₀ : Φ [] = 0)
    (A : OracleComp (D →ₒ R) α) (V : α → OracleComp (D →ₒ R) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (hN : Q_A + Q_V ≤ N) (bad : α → (D →ₒ R).QueryCache → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 (cacheOf z.2) →
      1 ≤ Φ z.2) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  rw [prEvent_romExperiment_eq_logExperiment A V fun r c ↦ r.2 = true ∧ bad r.1 c]
  exact prEvent_logExperiment_le_of_freshStepBelow N hΦ hΦ₀ A V Q_A Q_V hA hV hN
    (fun a ℓ ↦ bad a (cacheOf ℓ)) hbad

/-- **The `randomOracle` experiment bound through an order-aware potential, uncapped.** -/
theorem prEvent_romExperiment_le_of_logFreshStepBound {α : Type}
    {Φ : List (D × R) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ) (hΦ₀ : Φ [] = 0)
    (A : OracleComp (D →ₒ R) α) (V : α → OracleComp (D →ₒ R) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (bad : α → (D →ₒ R).QueryCache → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 (cacheOf z.2) →
      1 ≤ Φ z.2) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  rw [prEvent_romExperiment_eq_logExperiment A V fun r c ↦ r.2 = true ∧ bad r.1 c]
  exact prEvent_logExperiment_le hΦ hΦ₀ A V Q_A Q_V hA hV (fun a ℓ ↦ bad a (cacheOf ℓ)) hbad

end Rom

end
end LeanVM.Protocol
