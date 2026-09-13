import SphincsSecurity.Proof.Forced.SecretGuessForced
import SphincsSecurity.Proof.Base.WeightedQuery
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

noncomputable def hitTrial (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) : SPMF Bool :=
  if state.probes = slot then
    trial state.allowed coordinate candidate >>= fun hit =>
      if hit = true ∧ coordinate ∉ state.retired then pure hit else failure
  else trial state.allowed coordinate candidate

noncomputable def trialFactor (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) : ENNReal :=
  if state.probes = slot then
    if coordinate ∉ state.retired then trial state.allowed coordinate candidate true else 0
  else 1

theorem hitTrial_apply (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    hitTrial slot state coordinate candidate hit =
      trialFactor slot state coordinate candidate * forcedTrial slot state coordinate candidate hit := by
  by_cases hs : state.probes = slot
  · by_cases hc : coordinate ∉ state.retired
    · have hmass : hitTrial slot state coordinate candidate hit =
          if hit = true then trial state.allowed coordinate candidate true else 0 := by
        rw [hitTrial, if_pos hs, SPMF.bind_apply_eq_tsum]
        simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, false_and, if_false, true_and,
          hc, SPMF.failure_apply, mul_zero, add_zero]
        split <;> simp_all
      rw [hmass]
      by_cases hp : trial state.allowed coordinate candidate true = 0
      · simp only [trialFactor, if_pos hs, if_pos hc, hp, zero_mul, ite_self]
      · have he : EligibleAt slot state coordinate candidate := ⟨hs, hc, hp⟩
        simp only [trialFactor, if_pos hs, if_pos hc, forcedTrial, if_pos he, SPMF.pure_apply,
          mul_ite, mul_one, mul_zero]
    · simp only [hitTrial, trialFactor, if_pos hs, hc, and_false, if_false, SPMF.bind_apply_eq_tsum,
        SPMF.failure_apply, mul_zero, tsum_zero, zero_mul]
  · have he : ¬EligibleAt slot state coordinate candidate := fun h => hs h.1
    simp only [hitTrial, trialFactor, if_neg hs, forcedTrial, if_neg he, one_mul]

theorem hitTrial_bind_apply {Result : Type} (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (next : Bool → SPMF Result) (result : Result) :
    (hitTrial slot state coordinate candidate >>= next) result =
      trialFactor slot state coordinate candidate * (forcedTrial slot state coordinate candidate >>= next) result := by
  simp only [SPMF.bind_apply_eq_tsum, hitTrial_apply, mul_assoc, ENNReal.tsum_mul_left]

noncomputable def hitImpl (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => lazyImpl environment (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$> hitTrial slot state coordinate candidate
  | .inr (.inr coordinate) => lazyImpl environment (.inr (.inr coordinate))

noncomputable def forceFactor (slot : Nat) (state : State Coordinate Value Memory) :
    (World auxSpec Coordinate Value).Domain → ENNReal
  | .inr (.inl (coordinate, candidate)) => trialFactor slot state coordinate candidate
  | _ => 1

theorem hitImpl_apply (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory) :
    (hitImpl environment slot input).run state result =
      forceFactor slot state input * (forcedImpl environment slot input).run state result := by
  cases input with
  | inl input => simp only [hitImpl, forcedImpl, forceFactor, one_mul]
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [hitImpl, forcedImpl, forceFactor, StateT.run_mk, map_eq_bind_pure_comp,
            Function.comp_def]
          exact hitTrial_bind_apply slot state coordinate candidate
            (fun hit : Bool => pure (hit, afterTrial environment state coordinate candidate hit)) result
      | inr coordinate => simp only [hitImpl, forcedImpl, forceFactor, one_mul]

theorem hitImplRun_weighted_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | runWith (hitImpl environment slot) computation state] * payoff result) =
      ∑' result, Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (state, 1)] *
        (result.2.2 * payoff (result.1, result.2.1)) := by
  have h := WeightedQuery.run_payoff (hitImpl environment slot) (forcedImpl environment slot) (forceFactor slot)
    (hitImpl_apply environment slot) computation state 1 payoff
  simpa only [one_mul, runWith] using h

noncomputable def hitRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :=
  runWith (hitImpl environment slot) computation state >>= fun result =>
    if slot < result.2.probes then pure result else (failure : SPMF _)

noncomputable def forceWeight (slot : Nat) (state : State Coordinate Value Memory × ENNReal) : ENNReal :=
  if slot < state.1.probes then state.2 else 0

theorem hitRun_weighted_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitRun environment slot computation state] * payoff result) =
      ∑' result, Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (state, 1)] *
        (forceWeight slot result.2 * payoff (result.1, result.2.1)) := by
  have h := hitImplRun_weighted_forced environment slot computation state
    (fun result => if slot < result.2.probes then payoff result else 0)
  rw [hitRun, tsum_probOutput_bind_mul]
  convert h using 1
  · apply tsum_congr
    intro result
    congr 1
    by_cases hp : slot < result.2.probes
    · simp only [if_pos hp, tsum_probOutput_pure_mul]
    · simp only [if_neg hp, SPMF.probOutput_eq_apply, SPMF.failure_apply, zero_mul, tsum_zero]
  · apply tsum_congr
    intro result
    congr 1
    simp only [forceWeight, mul_ite, ite_mul, mul_zero, zero_mul]

end SphincsSecurity.Concrete.SecretGuessObservation
