import LeanVM.Protocol.ToVCVio.Rom.Potential
import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle

/-!
# Random-oracle potential tests

Statement locks for the potential bounds over lazy samplers and the logged oracle `loggedRO`
for two oracles; the inhabitants of `IsLazySampler` for VCVio's `randomOracle` and `loggedRO`;
first-match log lookup on concrete logs, each oracle reading its own entries.
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

end LeanVMTests.Protocol.Rom
