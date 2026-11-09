import LeanVM.Protocol.ToVCVio.Rom.Potential
import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle
import LeanVM.Protocol.ToVCVio.Rom.Bounds

/-!
# Random-oracle potential tests

Statement locks for the potential bounds over lazy samplers, VCVio's `randomOracle`, and the
logged oracle `loggedRO` for two oracles; the inhabitants of `IsLazySampler` for both
implementations; first-match log lookup on concrete logs, each oracle reading its own entries; a two-query computation on `Bool →ₒ Bool`, for which the birthday bound
gives `1/2` (the exact collision probability: the second fresh answer equals the first) and the
fresh-hit bound for the target `{true}` gives `1`; and a counterexample showing that the
increment `δ` does real work: the fresh-hit potential does not satisfy the step bound at
`δ = 0`.
-/

namespace LeanVMTests.Protocol.Rom

open OracleComp OracleSpec MeasureTheory LeanVM.Protocol LeanVM.Protocol.Rom
open scoped ENNReal

/-! ## Statement locks -/

example {ι : Type} {spec : OracleSpec.{0, 0} ι} [∀ t, SampleableType (spec.Range t)]
    [∀ t, Fintype (spec.Range t)] {σ : Type}
    {lookup : σ → (t : spec.Domain) → Option (spec.Range t)}
    {record : σ → (t : spec.Domain) → spec.Range t → σ}
    {impl : QueryImpl spec (StateT σ ProbComp)} (himpl : IsLazySampler lookup record impl)
    {α : Type} {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LazyFreshStepBound lookup record Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) (s₀ : σ) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + Q * δ :=
  prEvent_run_le_of_freshStepBound himpl hΦ oa Q hQ s₀ ev hev

example {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
    [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)] {α : Type}
    [MeasurableSpace (α × spec.QueryCache)] [DiscreteMeasurableSpace (α × spec.QueryCache)]
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) (c₀ : spec.QueryCache) :
    ∫⁻ z, Φ z.2 ∂𝒟[(simulateQ spec.randomOracle oa).run c₀] ≤ Φ c₀ + Q * δ :=
  lintegral_potential_run_randomOracle_le hΦ oa Q hQ c₀

example {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
    [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)] {α : Type}
    {Φ : spec.QueryCache → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : FreshStepBound Φ δ) (hΦ₀ : Φ ∅ = 0)
    (A : OracleComp spec α) (V : α → OracleComp spec Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (bad : α → spec.QueryCache → Prop)
    (hbad : ∀ z ∈ support (romExperiment A V), z.1.2 = true → bad z.1.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ :=
  prEvent_romExperiment_le hΦ hΦ₀ A V Q_A Q_V hA hV bad hbad

example {D₁ R₁ D₂ R₂ : Type} [DecidableEq D₁] [DecidableEq D₂] [SampleableType R₁]
    [SampleableType R₂] [Fintype R₁] [Fintype R₂] {α : Type}
    {Φ : List (LogEntry D₁ R₁ D₂ R₂) → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ) (hΦ : LogStepBelow N Φ δ)
    (hΦ₀ : Φ [] = 0) (A : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α)
    (V : α → OracleComp (Spec₂ D₁ R₁ D₂ R₂) Bool) (Q_A Q_V : ℕ)
    (hA : IsTotalQueryBound A Q_A) (hV : ∀ a, IsTotalQueryBound (V a) Q_V)
    (hN : Q_A + Q_V ≤ N) (bad : α → (Spec₂ D₁ R₁ D₂ R₂).QueryCache → Prop)
    (hbad : ∀ z ∈ support (logExperiment A V), z.1.2 = true → bad z.1.1 (cacheOf z.2) →
      1 ≤ Φ z.2) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤ (Q_A + Q_V : ℕ) * δ :=
  prEvent_romExperiment_le_of_logFreshStepBelow N hΦ hΦ₀ A V Q_A Q_V hA hV hN bad hbad

example {D₁ R₁ D₂ R₂ : Type} [DecidableEq D₁] [DecidableEq D₂] [SampleableType R₁]
    [SampleableType R₂] {α : Type} (oa : OracleComp (Spec₂ D₁ R₁ D₂ R₂) α) :
    (fun z ↦ (z.1, cacheOf z.2)) <$> (simulateQ loggedRO oa).run [] =
      (simulateQ (Spec₂ D₁ R₁ D₂ R₂).randomOracle oa).run ∅ :=
  map_run_simulateQ_loggedRO_nil oa

/-! ## Inhabitants -/

example : IsLazySampler (fun (c : (Bool →ₒ Bool).QueryCache) t ↦ c t)
    (fun c t u ↦ c.cacheQuery t u) (Bool →ₒ Bool).randomOracle :=
  randomOracle_isLazySampler

example : IsLazySampler (spec := Spec₂ Bool Bool Bool Bool) logLookup logRecord
    (loggedRO (D₁ := Bool) (R₁ := Bool) (D₂ := Bool) (R₂ := Bool)) :=
  loggedRO_isLazySampler

example : IsBudgetedPotential (birthdayPotential (D := Bool) (R := Bool)) :=
  isBudgetedPotential_birthdayPotential

example : FreshStepBound (hitPotential (D := Bool) ({true} : Finset Bool)) (1 / 2) := by
  simpa using freshStepBound_hitPotential (D := Bool) ({true} : Finset Bool)

/-! ## First-match lookup -/

#guard pairLookup [(1, 2), (1, 3)] (1 : ℕ) = some (2 : ℕ)
#guard pairLookup [(0, 5), (1, 3)] (1 : ℕ) = some (3 : ℕ)
#guard pairLookup [(0, 5), (1, 3)] (2 : ℕ) = (none : Option ℕ)
#guard pairLookup ([(0, 5)] ++ [(2, 7)]) (2 : ℕ) = some (7 : ℕ)

/-- A log of both oracles: each lookup reads its own oracle's entries. -/
def mixed : List (LogEntry ℕ ℕ ℕ ℕ) := [.inr (1, 9), .inl (1, 2), .inr (1, 4)]

#guard lookL mixed 1 = some 2
#guard lookR mixed 1 = some 9
#guard lookL mixed 0 = none

/-! ## A two-query computation -/

/-- Query the oracle at both points of `Bool`. -/
def twoQueries : OracleComp (Bool →ₒ Bool) (Bool × Bool) := do
  let a ← (Bool →ₒ Bool).query true
  let b ← (Bool →ₒ Bool).query false
  return (a, b)

theorem twoQueries_bound : IsTotalQueryBound twoQueries 2 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ ↦
    isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ ↦ trivial⟩⟩

/-- The birthday bound for two queries into a two-element range is `1/2`. -/
example : Pr{let z ← (simulateQ (Bool →ₒ Bool).randomOracle twoQueries).run ∅}[
    CacheHasCollision z.2] ≤ 1 / 2 := by
  refine (prEvent_cacheHasCollision_le twoQueries 2 twoQueries_bound).trans (le_of_eq ?_)
  norm_num
  rw [ENNReal.div_eq_inv_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by simp) (by simp), mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one]

/-- The fresh-hit bound for two queries and the target `{true}` is `1`. -/
example : Pr{let z ← (simulateQ (Bool →ₒ Bool).randomOracle twoQueries).run ∅}[
    CacheHits (({true} : Finset Bool) : Set Bool) z.2] ≤ 1 := by
  have h := prEvent_cacheHits_le ({true} : Finset Bool) twoQueries 2 twoQueries_bound ∅
    (by rintro ⟨t, u, h, _⟩; simp at h)
  refine h.trans (le_of_eq ?_)
  simp only [Finset.card_singleton, Fintype.card_bool, Nat.cast_ofNat, Nat.cast_one, one_div]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

/-! ## The increment does real work -/

/-- The fresh-hit potential for `{true}` does not satisfy the step bound at `δ = 0`: from the
empty cache a fresh query hits `true` with probability `1/2`. -/
example : ¬ FreshStepBound (hitPotential (D := Bool) ({true} : Finset Bool)) 0 := by
  intro h
  have := h ∅ true rfl
  have hhit : ∀ u, hitPotential (D := Bool) ({true} : Finset Bool)
      ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery true u) = if u = true then 1 else 0 := by
    intro u
    unfold hitPotential
    rw [cacheHits_cacheQuery_iff _ _ _ _ rfl]
    simp [CacheHits]
  have hzero : hitPotential (D := Bool) ({true} : Finset Bool) ∅ = 0 := by
    simp [hitPotential, CacheHits]
  simp only [hhit, hzero, Fintype.sum_bool] at this
  norm_num at this

end LeanVMTests.Protocol.Rom
