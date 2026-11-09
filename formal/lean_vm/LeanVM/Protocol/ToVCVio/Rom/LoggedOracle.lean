/-
  LeanVM.Protocol.ToVCVio.Rom.LoggedOracle

  The lazy random oracle for two independent oracles over one ordered log of fresh queries, its
  potential bounds, and its equivalence with VCVio's `randomOracle`. Candidate for VCVio.
-/

module

public import LeanVM.Protocol.ToVCVio.Rom.Potential

/-!
# The logged lazy random oracle for two oracles

`Rom.loggedRO` is the lazy random oracle for the sum `(D₁ →ₒ R₁) + (D₂ →ₒ R₂)` of two oracles,
whose state is the ordered list of the fresh queries made so far to either oracle,
`ℓ : List ((D₁ × R₁) ⊕ (D₂ × R₂))`. A query at `.inl x` looks `x` up among the left entries of
the log, first match first (`lookL`), and a query at `.inr s` among the right entries (`lookR`);
a fresh point draws a uniform answer and appends the entry at the end of the log. Unlike VCVio's
`QueryCache`, the log records the order of fresh queries across both oracles, so a potential on
logs can tell a query that predicts a value referenced earlier from one made in the honest order.

The bounds of `LeanVM.Protocol.ToVCVio.Rom.Potential` apply to `loggedRO`
(`loggedRO_isLazySampler`). For `Φ` on logs whose expectation rises by at most `δ` at every
fresh query to either oracle (`LogFreshStepBound Φ δ`, `logFreshStepBound_iff`), a computation
with at most `Q` queries run from `ℓ₀` has expected final potential at most `Φ ℓ₀ + Q · δ`
(`lintegral_run_loggedRO_le_of_freshStepBound`), and an event forcing `1 ≤ Φ` of the final log
has probability at most `Φ ℓ₀ + Q · δ` (`prEvent_run_loggedRO_le_of_freshStepBound`). The
length-capped form (`prEvent_run_loggedRO_le_of_freshStepBelow`) needs the step bound only at
logs shorter than a cap `N ≥ |ℓ₀| + Q`.

The log determines a cache, its lookup function (`cacheOf`). Running `loggedRO` from `ℓ₀` and
reading the final log as a cache has the same distribution of output and cache as VCVio's
`randomOracle` run from `cacheOf ℓ₀` (`map_run_simulateQ_loggedRO`). So a bound proved with an
order-aware potential on logs is a bound about `randomOracle`
(`prEvent_romExperiment_le_of_logFreshStepBelow`).
-/

namespace LeanVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

namespace Rom

variable {D₁ R₁ D₂ R₂ : Type}

/-- The two oracles: `D₁ →ₒ R₁` at `.inl` and `D₂ →ₒ R₂` at `.inr`. -/
abbrev Spec₂ (D₁ R₁ D₂ R₂ : Type) : OracleSpec (D₁ ⊕ D₂) := (D₁ →ₒ R₁) + (D₂ →ₒ R₂)

/-- A log entry: a fresh query to one of the two oracles, with its answer. -/
abbrev LogEntry (D₁ R₁ D₂ R₂ : Type) : Type := (D₁ × R₁) ⊕ (D₂ × R₂)

/-! ## Logs -/

/-- The answer a list of pairs gives at `t`: the output of its first pair with input `t`. -/
def pairLookup {D R : Type} [DecidableEq D] : List (D × R) → D → Option R
  | [], _ => none
  | e :: ℓ, t => if e.1 = t then some e.2 else pairLookup ℓ t

/-- The left entries of a log. -/
def leftOf : List (LogEntry D₁ R₁ D₂ R₂) → List (D₁ × R₁) :=
  List.filterMap fun e ↦ match e with
    | .inl p => some p
    | .inr _ => none

/-- The right entries of a log. -/
def rightOf : List (LogEntry D₁ R₁ D₂ R₂) → List (D₂ × R₂) :=
  List.filterMap fun e ↦ match e with
    | .inl _ => none
    | .inr p => some p

@[simp] theorem leftOf_nil : leftOf ([] : List (LogEntry D₁ R₁ D₂ R₂)) = [] := rfl

@[simp] theorem rightOf_nil : rightOf ([] : List (LogEntry D₁ R₁ D₂ R₂)) = [] := rfl

@[simp] theorem leftOf_append (ℓ ℓ' : List (LogEntry D₁ R₁ D₂ R₂)) :
    leftOf (ℓ ++ ℓ') = leftOf ℓ ++ leftOf ℓ' := List.filterMap_append

@[simp] theorem rightOf_append (ℓ ℓ' : List (LogEntry D₁ R₁ D₂ R₂)) :
    rightOf (ℓ ++ ℓ') = rightOf ℓ ++ rightOf ℓ' := List.filterMap_append

@[simp] theorem leftOf_inl (p : D₁ × R₁) :
    leftOf ([.inl p] : List (LogEntry D₁ R₁ D₂ R₂)) = [p] := rfl

@[simp] theorem leftOf_inr (p : D₂ × R₂) :
    leftOf ([.inr p] : List (LogEntry D₁ R₁ D₂ R₂)) = [] := rfl

@[simp] theorem rightOf_inl (p : D₁ × R₁) :
    rightOf ([.inl p] : List (LogEntry D₁ R₁ D₂ R₂)) = [] := rfl

@[simp] theorem rightOf_inr (p : D₂ × R₂) :
    rightOf ([.inr p] : List (LogEntry D₁ R₁ D₂ R₂)) = [p] := rfl

theorem mem_leftOf {ℓ : List (LogEntry D₁ R₁ D₂ R₂)} {p : D₁ × R₁} :
    p ∈ leftOf ℓ ↔ .inl p ∈ ℓ := by
  simp only [leftOf, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hp⟩
    rcases e with q | q <;> simp at hp
    subst hp; exact he
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_rightOf {ℓ : List (LogEntry D₁ R₁ D₂ R₂)} {p : D₂ × R₂} :
    p ∈ rightOf ℓ ↔ .inr p ∈ ℓ := by
  simp only [rightOf, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hp⟩
    rcases e with q | q <;> simp at hp
    subst hp; exact he
  · intro h; exact ⟨_, h, rfl⟩

variable [DecidableEq D₁] [DecidableEq D₂]

/-- The answer of the left oracle in a log. -/
def lookL (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (x : D₁) : Option R₁ := pairLookup (leftOf ℓ) x

/-- The answer of the right oracle in a log. -/
def lookR (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (s : D₂) : Option R₂ := pairLookup (rightOf ℓ) s

/-- The answer a log gives at a query of either oracle. -/
def logLookup (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) :
    (t : D₁ ⊕ D₂) → Option ((Spec₂ D₁ R₁ D₂ R₂).Range t)
  | .inl x => lookL ℓ x
  | .inr s => lookR ℓ s

/-- The log after a fresh answer at a query of either oracle. -/
def logRecord (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) :
    (t : D₁ ⊕ D₂) → (Spec₂ D₁ R₁ D₂ R₂).Range t → List (LogEntry D₁ R₁ D₂ R₂)
  | .inl x, u => ℓ ++ [.inl (x, u)]
  | .inr s, u => ℓ ++ [.inr (s, u)]

section Pairs

variable {D R : Type} [DecidableEq D]

@[simp] theorem pairLookup_nil (t : D) : pairLookup ([] : List (D × R)) t = none := rfl

theorem pairLookup_cons (e : D × R) (ℓ : List (D × R)) (t : D) :
    pairLookup (e :: ℓ) t = if e.1 = t then some e.2 else pairLookup ℓ t := rfl

/-- A list has no answer at `t` exactly when `t` is not among its inputs. -/
theorem pairLookup_eq_none_iff (ℓ : List (D × R)) (t : D) :
    pairLookup ℓ t = none ↔ t ∉ ℓ.map Prod.fst := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    rw [pairLookup_cons]
    by_cases h : e.1 = t
    · simp [h]
    · simp [h, ih, Ne.symm h]

/-- A lookup after appending: the earlier answer, or the appended one. -/
theorem pairLookup_append (ℓ ℓ' : List (D × R)) (t : D) :
    pairLookup (ℓ ++ ℓ') t = (pairLookup ℓ t).or (pairLookup ℓ' t) := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    simp only [List.cons_append, pairLookup_cons]
    split
    · rfl
    · exact ih

/-- Appending a pair at a point the list does not answer adds that one answer. -/
theorem pairLookup_append_singleton (ℓ : List (D × R)) (t t' : D) (u : R)
    (h : pairLookup ℓ t = none) :
    pairLookup (ℓ ++ [(t, u)]) t' = if t' = t then some u else pairLookup ℓ t' := by
  rw [pairLookup_append]
  by_cases ht : t' = t
  · subst ht; simp [h, pairLookup_cons]
  · simp [ht, pairLookup_cons, Ne.symm ht]

/-- A lookup is the first pair with the input. -/
theorem pairLookup_eq_some_iff (ℓ : List (D × R)) (x : D) (v : R) :
    pairLookup ℓ x = some v ↔
      ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i] = (x, v) ∧ pairLookup (ℓ.take i) x = none := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    rw [pairLookup_cons]
    by_cases he : e.1 = x
    · simp only [he, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, by simp [← he], by simp⟩
      · rintro ⟨i, hi, hei, hn⟩
        cases i with
        | zero => simp at hei; subst hei; rfl
        | succ i => simp [pairLookup_cons, he] at hn
    · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h he), ih]
      constructor
      · rintro ⟨i, hi, hei, hn⟩
        exact ⟨i + 1, by simpa using hi, by simpa using hei, by simp [pairLookup_cons, he, hn]⟩
      · rintro ⟨i, hi, hei, hn⟩
        cases i with
        | zero => simp at hei; exact absurd (by rw [hei]) he
        | succ i =>
          refine ⟨i, by simpa using hi, by simpa using hei, ?_⟩
          simpa [pairLookup_cons, he] using hn

end Pairs

omit [DecidableEq D₂] in
/-- The left lookup sees only left entries. -/
theorem lookL_append (ℓ ℓ' : List (LogEntry D₁ R₁ D₂ R₂)) (x : D₁) :
    lookL (ℓ ++ ℓ') x = (lookL ℓ x).or (lookL ℓ' x) := by
  simp only [lookL, leftOf_append, pairLookup_append]

omit [DecidableEq D₁] in
/-- The right lookup sees only right entries. -/
theorem lookR_append (ℓ ℓ' : List (LogEntry D₁ R₁ D₂ R₂)) (s : D₂) :
    lookR (ℓ ++ ℓ') s = (lookR ℓ s).or (lookR ℓ' s) := by
  simp only [lookR, rightOf_append, pairLookup_append]

omit [DecidableEq D₂] in
@[simp] theorem lookL_nil (x : D₁) : lookL ([] : List (LogEntry D₁ R₁ D₂ R₂)) x = none := rfl

omit [DecidableEq D₁] in
@[simp] theorem lookR_nil (s : D₂) : lookR ([] : List (LogEntry D₁ R₁ D₂ R₂)) s = none := rfl

omit [DecidableEq D₂] in
@[simp] theorem lookL_inr (p : D₂ × R₂) (x : D₁) :
    lookL ([.inr p] : List (LogEntry D₁ R₁ D₂ R₂)) x = none := rfl

omit [DecidableEq D₁] in
@[simp] theorem lookR_inl (p : D₁ × R₁) (s : D₂) :
    lookR ([.inl p] : List (LogEntry D₁ R₁ D₂ R₂)) s = none := rfl

omit [DecidableEq D₂] in
theorem lookL_inl (x' : D₁) (u : R₁) (x : D₁) :
    lookL ([.inl (x', u)] : List (LogEntry D₁ R₁ D₂ R₂)) x = if x' = x then some u else none := by
  simp [lookL, pairLookup_cons]

omit [DecidableEq D₁] in
theorem lookR_inr (s' : D₂) (u : R₂) (s : D₂) :
    lookR ([.inr (s', u)] : List (LogEntry D₁ R₁ D₂ R₂)) s = if s' = s then some u else none := by
  simp [lookR, pairLookup_cons]

omit [DecidableEq D₂] in
/-- A left lookup is absent exactly when the point is not a left input. -/
theorem lookL_eq_none_iff (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (x : D₁) :
    lookL ℓ x = none ↔ x ∉ (leftOf ℓ).map Prod.fst := pairLookup_eq_none_iff _ _

omit [DecidableEq D₁] in
/-- A right lookup is absent exactly when the point is not a right input. -/
theorem lookR_eq_none_iff (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (s : D₂) :
    lookR ℓ s = none ↔ s ∉ (rightOf ℓ).map Prod.fst := pairLookup_eq_none_iff _ _

/-- The cache a log determines: its lookup function. -/
def cacheOf (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) : (Spec₂ D₁ R₁ D₂ R₂).QueryCache :=
  QueryCache.ofFn (logLookup ℓ)

@[simp] theorem cacheOf_apply (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (t : D₁ ⊕ D₂) :
    cacheOf ℓ t = logLookup ℓ t := rfl

@[simp] theorem cacheOf_nil : cacheOf ([] : List (LogEntry D₁ R₁ D₂ R₂)) = ∅ :=
  QueryCache.ext fun t ↦ by rcases t with x | s <;> rfl

theorem logLookup_logRecord (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (t : D₁ ⊕ D₂)
    (u : (Spec₂ D₁ R₁ D₂ R₂).Range t) (h : logLookup ℓ t = none) (t' : D₁ ⊕ D₂) :
    logLookup (logRecord ℓ t u) t' = if h' : t = t' then some (h' ▸ u) else logLookup ℓ t' := by
  rcases t with x | s <;> rcases t' with x' | s'
  · change lookL (ℓ ++ [.inl (x, u)]) x' = _
    rw [lookL_append, lookL_inl]
    change lookL ℓ x = none at h
    by_cases hx : x = x'
    · subst hx; simp [h]
    · simp [hx]; rfl
  · change lookR (ℓ ++ [.inl (x, u)]) s' = _
    rw [lookR_append, lookR_inl]; simp; rfl
  · change lookL (ℓ ++ [.inr (s, u)]) x' = _
    rw [lookL_append, lookL_inr]; simp; rfl
  · change lookR (ℓ ++ [.inr (s, u)]) s' = _
    rw [lookR_append, lookR_inr]
    change lookR ℓ s = none at h
    by_cases hs : s = s'
    · subst hs; simp [h]
    · simp [hs]; rfl

/-- Appending a fresh entry to a log records it in the cache. -/
theorem cacheOf_logRecord (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (t : D₁ ⊕ D₂)
    (u : (Spec₂ D₁ R₁ D₂ R₂).Range t) (h : logLookup ℓ t = none) :
    cacheOf (logRecord ℓ t u) = (cacheOf ℓ).cacheQuery t u := by
  refine QueryCache.ext fun t' ↦ ?_
  rw [cacheOf_apply, logLookup_logRecord ℓ t u h t']
  by_cases ht : t = t'
  · subst ht
    simp
  · simp [ht, QueryCache.cacheQuery_of_ne _ _ (Ne.symm ht)]

/-! ## The logged random oracle -/

variable [SampleableType R₁] [SampleableType R₂]

/-- The lazy random oracle over an ordered log: a point the log answers gets that answer, and a
fresh point gets a uniform answer appended at the end of the log. -/
def loggedRO :
    QueryImpl (Spec₂ D₁ R₁ D₂ R₂) (StateT (List (LogEntry D₁ R₁ D₂ R₂)) ProbComp) :=
  fun t ↦ StateT.mk fun ℓ ↦
    match logLookup ℓ t with
    | some u => pure (u, ℓ)
    | none => ($ᵗ (Spec₂ D₁ R₁ D₂ R₂).Range t) >>= fun u ↦ pure (u, logRecord ℓ t u)

/-- `loggedRO` is a lazy sampler over logs. -/
theorem loggedRO_isLazySampler :
    IsLazySampler (spec := Spec₂ D₁ R₁ D₂ R₂) logLookup logRecord
      (loggedRO (D₁ := D₁) (R₁ := R₁) (D₂ := D₂) (R₂ := R₂)) := by
  intro t ℓ
  rcases h : logLookup ℓ t with _ | u <;> simp [loggedRO, h]

/-- **The bridge to `randomOracle`.** Running `loggedRO` from `ℓ₀` and reading the final log as
a cache is running VCVio's `randomOracle` from `cacheOf ℓ₀`. -/
theorem map_run_simulateQ_loggedRO {α : Type} (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (ℓ₀ : List (LogEntry D₁ R₁ D₂ R₂)) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> (simulateQ loggedRO oa).run ℓ₀ =
      (simulateQ (Spec₂ D₁ R₁ D₂ R₂).randomOracle oa).run (cacheOf ℓ₀) :=
  map_run_simulateQ_eq_of_isLazySampler loggedRO_isLazySampler randomOracle_isLazySampler
    cacheOf (fun _ _ ↦ rfl) (fun ℓ t u h ↦ cacheOf_logRecord ℓ t u h) oa ℓ₀

/-- The bridge from the empty log. -/
theorem map_run_simulateQ_loggedRO_nil {α : Type} (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> (simulateQ loggedRO oa).run [] =
      (simulateQ (Spec₂ D₁ R₁ D₂ R₂).randomOracle oa).run ∅ := by
  rw [map_run_simulateQ_loggedRO, cacheOf_nil]

/-- Events of a `randomOracle` run from the empty cache are events of the `loggedRO` run from
the empty log, read through `cacheOf`. -/
theorem prEvent_run_randomOracle_eq_loggedRO {α : Type}
    (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (ev : α → (Spec₂ D₁ R₁ D₂ R₂).QueryCache → Prop) :
    Pr{let z ← (simulateQ (Spec₂ D₁ R₁ D₂ R₂).randomOracle oa).run ∅}[ev z.1 z.2] =
      Pr{let z ← (simulateQ loggedRO oa).run []}[ev z.1 (cacheOf z.2)] := by
  rw [← cacheOf_nil (D₁ := D₁) (R₁ := R₁) (D₂ := D₂) (R₂ := R₂)]
  exact prEvent_run_eq_of_isLazySampler loggedRO_isLazySampler randomOracle_isLazySampler
    cacheOf (fun _ _ ↦ rfl) (fun ℓ t u h ↦ cacheOf_logRecord ℓ t u h) oa [] ev

/-! ## Potentials on logs -/

variable [Fintype R₁] [Fintype R₂]

/-- `Φ` rises by at most `δ` in expectation at every fresh logged query, to either oracle. -/
abbrev LogFreshStepBound (Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞) (δ : ℝ≥0∞) : Prop :=
  LazyFreshStepBound (spec := Spec₂ D₁ R₁ D₂ R₂) logLookup logRecord Φ δ

omit [SampleableType R₁] [SampleableType R₂] in
/-- The step condition, one oracle at a time, in terms of the log's inputs. -/
theorem logFreshStepBound_iff (Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞) (δ : ℝ≥0∞) :
    LogFreshStepBound Φ δ ↔
      (∀ (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (x : D₁), x ∉ (leftOf ℓ).map Prod.fst →
        (∑ u : R₁, Φ (ℓ ++ [.inl (x, u)])) / Fintype.card R₁ ≤ Φ ℓ + δ) ∧
      (∀ (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (s : D₂), s ∉ (rightOf ℓ).map Prod.fst →
        (∑ u : R₂, Φ (ℓ ++ [.inr (s, u)])) / Fintype.card R₂ ≤ Φ ℓ + δ) := by
  constructor
  · intro h
    exact ⟨fun ℓ x hx ↦ h ℓ (.inl x) ((lookL_eq_none_iff ℓ x).mpr hx),
      fun ℓ s hs ↦ h ℓ (.inr s) ((lookR_eq_none_iff ℓ s).mpr hs)⟩
  · rintro ⟨h1, h2⟩ ℓ t ht
    rcases t with x | s
    · exact h1 ℓ x ((lookL_eq_none_iff ℓ x).mp ht)
    · exact h2 ℓ s ((lookR_eq_none_iff ℓ s).mp ht)

/-- The length-capped step condition, one oracle at a time. -/
def LogStepBelow (N : ℕ) (Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞) (δ : ℝ≥0∞) : Prop :=
  (∀ (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (x : D₁), ℓ.length < N → x ∉ (leftOf ℓ).map Prod.fst →
    (∑ u : R₁, Φ (ℓ ++ [.inl (x, u)])) / Fintype.card R₁ ≤ Φ ℓ + δ) ∧
  (∀ (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (s : D₂), ℓ.length < N → s ∉ (rightOf ℓ).map Prod.fst →
    (∑ u : R₂, Φ (ℓ ++ [.inr (s, u)])) / Fintype.card R₂ ≤ Φ ℓ + δ)

omit [SampleableType R₁] [SampleableType R₂] in
theorem logStepBelow_lazy {N : ℕ} {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞}
    (h : LogStepBelow N Φ δ) :
    ∀ (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (t : D₁ ⊕ D₂), ℓ.length < N → logLookup ℓ t = none →
      (∑ u, Φ (logRecord ℓ t u)) / Fintype.card ((Spec₂ D₁ R₁ D₂ R₂).Range t) ≤ Φ ℓ + δ := by
  intro ℓ t hN ht
  rcases t with x | s
  · exact h.1 ℓ x hN ((lookL_eq_none_iff ℓ x).mp ht)
  · exact h.2 ℓ s hN ((lookR_eq_none_iff ℓ s).mp ht)

omit [DecidableEq D₁] [DecidableEq D₂] [SampleableType R₁] [SampleableType R₂] [Fintype R₁]
  [Fintype R₂] in
theorem length_logRecord (ℓ : List (LogEntry D₁ R₁ D₂ R₂)) (t : D₁ ⊕ D₂)
    (u : (Spec₂ D₁ R₁ D₂ R₂).Range t) : (logRecord ℓ t u).length = ℓ.length + 1 := by
  rcases t with x | s <;> simp [logRecord]

/-- **The potential bound for `loggedRO`.** -/
theorem lintegral_run_loggedRO_le_of_freshStepBound {α : Type}
    [MeasurableSpace (α × List (LogEntry D₁ R₁ D₂ R₂))]
    [DiscreteMeasurableSpace (α × List (LogEntry D₁ R₁ D₂ R₂))]
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (LogEntry D₁ R₁ D₂ R₂)) (g : α × List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ loggedRO oa).run ℓ₀), g z ≤ Φ z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ loggedRO oa).run ℓ₀] ≤ Φ ℓ₀ + Q * δ :=
  lintegral_run_le_of_freshStepBound loggedRO_isLazySampler hΦ oa Q hQ ℓ₀ g hg

/-- **Markov at one for `loggedRO`.** -/
theorem prEvent_run_loggedRO_le_of_freshStepBound {α : Type}
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (LogEntry D₁ R₁ D₂ R₂)) (ev : α → List (LogEntry D₁ R₁ D₂ R₂) → Prop)
    (hev : ∀ z ∈ support ((simulateQ loggedRO oa).run ℓ₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ loggedRO oa).run ℓ₀}[ev z.1 z.2] ≤ Φ ℓ₀ + Q * δ :=
  prEvent_run_le_of_freshStepBound loggedRO_isLazySampler hΦ oa Q hQ ℓ₀ ev hev

/-- **Markov at one for `loggedRO`, length-capped form.** -/
theorem prEvent_run_loggedRO_le_of_freshStepBelow {α : Type}
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ) (hΦ : LogStepBelow N Φ δ)
    (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (ℓ₀ : List (LogEntry D₁ R₁ D₂ R₂)) (hℓ₀ : ℓ₀.length + Q ≤ N)
    (ev : α → List (LogEntry D₁ R₁ D₂ R₂) → Prop)
    (hev : ∀ z ∈ support ((simulateQ loggedRO oa).run ℓ₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ loggedRO oa).run ℓ₀}[ev z.1 z.2] ≤ Φ ℓ₀ + Q * δ :=
  prEvent_run_le_of_freshStepBelow loggedRO_isLazySampler List.length N
    (fun ℓ t u _ ↦ (length_logRecord ℓ t u).le) (logStepBelow_lazy hΦ) oa Q hQ ℓ₀ hℓ₀ ev hev

/-! ## The logged experiment -/

/-- The adversary-then-verifier experiment over the log: the adversary `A` runs against
`loggedRO` from the empty log, then the verifier `V` on the adversary's output continues with
the same log. The outcome is the adversary's output, the verdict, and the final log. -/
noncomputable def logExperiment {α : Type} (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool) :
    ProbComp ((α × Bool) × List (LogEntry D₁ R₁ D₂ R₂)) :=
  (simulateQ loggedRO (A >>= fun a ↦ (a, ·) <$> V a)).run []

omit [Fintype R₁] [Fintype R₂] in
/-- The experiment over `randomOracle` is the logged experiment read through `cacheOf`. -/
theorem map_logExperiment {α : Type} (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> logExperiment A V = romExperiment A V :=
  map_run_simulateQ_loggedRO_nil _

omit [Fintype R₁] [Fintype R₂] in
/-- Events of the `randomOracle` experiment are events of the logged experiment read through
`cacheOf`. -/
theorem prEvent_romExperiment_eq_logExperiment {α : Type}
    (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α) (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool)
    (ev : (α × Bool) → (Spec₂ D₁ R₁ D₂ R₂).QueryCache → Prop) :
    Pr{let z ← romExperiment A V}[ev z.1 z.2] =
      Pr{let z ← logExperiment A V}[ev z.1 (cacheOf z.2)] :=
  prEvent_run_randomOracle_eq_loggedRO _ ev

/-- **The logged experiment bound.** -/
theorem prEvent_logExperiment_le {α : Type}
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (hΦ₀ : Φ [] = 0) (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (bad : α → List (LogEntry D₁ R₁ D₂ R₂) → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← logExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  have h := prEvent_run_loggedRO_le_of_freshStepBound hΦ _ (Q_A + Q_V)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (V a) _ Q_V _ _).mpr (hV a)) []
    (fun r ℓ ↦ r.2 = true ∧ bad r.1 ℓ) (fun z hz h ↦ hbad z hz h.1 h.2)
  rwa [hΦ₀, zero_add] at h

/-- **The logged experiment bound, length-capped form.** -/
theorem prEvent_logExperiment_le_of_freshStepBelow {α : Type}
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ) (hΦ : LogStepBelow N Φ δ)
    (hΦ₀ : Φ [] = 0) (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (hN : Q_A + Q_V ≤ N) (bad : α → List (LogEntry D₁ R₁ D₂ R₂) → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← logExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  have h := prEvent_run_loggedRO_le_of_freshStepBelow N hΦ _ (Q_A + Q_V)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (V a) _ Q_V _ _).mpr (hV a)) []
    (by simpa using hN) (fun r ℓ ↦ r.2 = true ∧ bad r.1 ℓ) (fun z hz h ↦ hbad z hz h.1 h.2)
  rwa [hΦ₀, zero_add] at h

/-- **The `randomOracle` experiment bound through an order-aware potential.** If `Φ` on logs
vanishes on the empty log and rises by at most `δ` per fresh query to either oracle at logs
shorter than `N ≥ Q_A + Q_V`, then in VCVio's `romExperiment` an adversary with at most `Q_A`
queries and a verifier with at most `Q_V` queries make the verifier accept while `bad` holds of
the adversary's output and the final cache with probability at most `(Q_A + Q_V) · δ`, provided
that on every reachable outcome of the logged experiment, acceptance and `bad` of the log's
cache force `1 ≤ Φ` of the final log. -/
theorem prEvent_romExperiment_le_of_logFreshStepBelow {α : Type}
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ) (hΦ : LogStepBelow N Φ δ)
    (hΦ₀ : Φ [] = 0) (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (hN : Q_A + Q_V ≤ N) (bad : α → (Spec₂ D₁ R₁ D₂ R₂).QueryCache → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 (cacheOf z.2) →
      1 ≤ Φ z.2) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ := by
  rw [prEvent_romExperiment_eq_logExperiment A V fun r c ↦ r.2 = true ∧ bad r.1 c]
  exact prEvent_logExperiment_le_of_freshStepBelow N hΦ hΦ₀ A V Q_A Q_V hA hV hN
    (fun a ℓ ↦ bad a (cacheOf ℓ)) hbad

end Rom

end
end LeanVM.Protocol
