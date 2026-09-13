import SphincsSecurity.Proof.Forced.SecretGuessForceLikelihood
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

theorem forceFactor_le_one (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain) : forceFactor slot state input ≤ 1 := by
  cases input with
  | inl input => exact le_rfl
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [forceFactor, trialFactor]
          split
          · split
            · simpa only [SPMF.probOutput_eq_apply] using
                (show Pr[= true | trial state.allowed coordinate candidate] ≤ 1 from probOutput_le_one)
            · exact bot_le
          · exact le_rfl
      | inr coordinate => exact le_rfl

theorem forceFactor_weight_bound (environment : Environment auxSpec Coordinate Value Memory) (size budget slot : Nat)
    (hslot : slot ≤ budget) (state : State Coordinate Value Memory) (weight : ENNReal)
    (hs : Invariant size state) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (hw : weight ≤ 1) (hlate : slot < state.probes → weight ≤ ((size - budget : Nat) : ENNReal)⁻¹)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedImpl environment slot input).run state result ≠ 0) :
    weight * forceFactor slot state input ≤ 1 ∧
      (slot < result.2.probes → weight * forceFactor slot state input ≤ ((size - budget : Nat) : ENNReal)⁻¹) := by
  have hm : weight * forceFactor slot state input ≤ weight := mul_le_of_le_one_right' (forceFactor_le_one slot state input)
  refine ⟨hm.trans hw, ?_⟩
  intro hafter
  by_cases hb : slot < state.probes
  · exact hm.trans (hlate hb)
  have hp := forcedImpl_probes environment slot state input result hr
  cases input with
  | inl input => simp only [probeStep, Nat.add_zero] at hp; omega
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          change result.2.probes = state.probes + 1 at hp
          have he : state.probes = slot := by omega
          simp only [forceFactor, trialFactor, if_pos he]
          split
          next hc =>
            exact (mul_le_of_le_one_left' hw).trans
              (trial_true_le size budget state hs ha (he ▸ hslot) coordinate hc candidate)
          next hc => simp only [mul_zero]; exact bot_le
      | inr coordinate => simp only [probeStep, Nat.add_zero] at hp; omega

theorem weightedForcedRun_weight_bound [Fintype Value] [Nonempty Value] {Result : Type}
    (environment : Environment auxSpec Coordinate Value Memory) (budget slot : Nat) (hslot : slot ≤ budget)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory)
    (result : Result × State Coordinate Value Memory × ENNReal)
    (hr : WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (initialState memory, 1) result ≠ 0) :
    forceWeight slot result.2 ≤ ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ := by
  let valid (state : State Coordinate Value Memory × ENNReal) : Prop :=
    Invariant (Fintype.card Value) state.1 ∧ (∀ coordinate, (state.1.allowed coordinate).Nonempty) ∧
      state.2 ≤ 1 ∧ (slot < state.1.probes → state.2 ≤ ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹)
  have hstep (state : State Coordinate Value Memory × ENNReal) (hs : valid state)
      (input : (World auxSpec Coordinate Value).Domain)
      (middle : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
      (hm : (forcedImpl environment slot input).run state.1 middle ≠ 0) :
      valid (middle.2, state.2 * forceFactor slot state.1 input) := by
    have hlazy : lazyRun environment (liftM ((World auxSpec Coordinate Value).query input)) state.1 middle ≠ 0 := by
      simpa only [lazyRun, runWith, simulateQ_spec_query] using forcedImpl_nonzero environment slot state.1 input middle hm
    exact ⟨lazyRun_invariant environment (Fintype.card Value) _ state.1 hs.1 middle hlazy,
      lazyRun_nonempty environment _ state.1 hs.2.1 middle hlazy,
      forceFactor_weight_bound environment (Fintype.card Value) budget slot hslot state.1 state.2 hs.1 hs.2.1
        hs.2.2.1 hs.2.2.2 input middle hm⟩
  have hinitial : valid (initialState memory, 1) :=
    ⟨initialState_invariant memory, fun _ => Finset.univ_nonempty, le_rfl, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  have h := WeightedQuery.run_preserves (forcedImpl environment slot) (forceFactor slot) valid hstep
    computation (initialState memory, 1) hinitial result hr
  rw [forceWeight]
  split
  · exact h.2.2.2 ‹_›
  · exact bot_le

theorem hitRun_payoff_le_forced [Fintype Value] [Nonempty Value] {Result : Type}
    (environment : Environment auxSpec Coordinate Value Memory) (budget slot : Nat) (hslot : slot ≤ budget)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitRun environment slot computation (initialState memory)] * payoff result) ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        (∑' result, Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result) := by
  rw [hitRun_weighted_forced]
  have hforget := congrArg (fun law : SPMF (Result × State Coordinate Value Memory) =>
    ∑' result, Pr[= result | law] * payoff result)
    (WeightedQuery.run_forget (forcedImpl environment slot) (forceFactor slot) computation (initialState memory, 1))
  rw [tsum_probOutput_map_mul] at hforget
  rw [← show (∑' result, Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot)
      computation (initialState memory, 1)] * payoff (result.1, result.2.1)) =
      (∑' result, Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result) from hforget,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hz : WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (initialState memory, 1) result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, mul_zero, le_refl]
  · calc
      _ ≤ Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot)
          computation (initialState memory, 1)] *
          (((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ * payoff (result.1, result.2.1)) :=
        mul_le_mul' le_rfl (mul_le_mul' (weightedForcedRun_weight_bound environment budget slot hslot computation memory result hz) le_rfl)
      _ = _ := by ring

end SphincsSecurity.Concrete.SecretGuessObservation
