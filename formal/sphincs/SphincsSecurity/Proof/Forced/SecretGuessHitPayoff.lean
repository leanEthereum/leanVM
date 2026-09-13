import SphincsSecurity.Proof.Forced.SecretGuessHitSum
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Fintype Value] [Nonempty Value]

omit [Nonempty Value] in
theorem lazyRun_guess_payoff_le_sum {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | lazyRun environment computation (initialState memory)] *
      (if result.2.guesses.Nonempty then payoff result else 0)) ≤
      ∑ slot ∈ Finset.range budget, ∑' result,
        Pr[= result | hitRun environment slot computation (initialState memory)] * payoff result := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hz : lazyRun environment computation (initialState memory) result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul]
    exact bot_le
  by_cases hg : result.2.guesses.Nonempty
  · rw [if_pos hg]
    have h := lazyRun_new_guesses_le_sum environment computation (initialState memory) result budget (hbudget result hz)
      (show result.2.guesses ≠ (initialState memory : State Coordinate Value Memory).guesses from hg.ne_empty)
    have hp := mul_le_mul' h (le_rfl : payoff result ≤ payoff result)
    simpa only [initialState, ← Finset.range_eq_Ico, Finset.sum_mul, SPMF.probOutput_eq_apply] using hp
  · simp only [if_neg hg, mul_zero]
    exact bot_le

theorem lazyRun_guess_payoff_le_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | lazyRun environment computation (initialState memory)] *
      (if result.2.guesses.Nonempty then payoff result else 0)) ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result := by
  apply (lazyRun_guess_payoff_le_sum environment computation memory budget hbudget payoff).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro slot hslot
  exact hitRun_payoff_le_forced environment budget slot (Finset.mem_range.mp hslot).le computation memory payoff

theorem lazyRun_event_le_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget)
    (event : Result × State Coordinate Value Memory → Prop) (payoff : Result × State Coordinate Value Memory → ENNReal)
    (hevent : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → event result →
      result.2.guesses.Nonempty ∧ 1 ≤ payoff result) :
    Pr[event | lazyRun environment computation (initialState memory)] ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => if result.2.guesses.Nonempty then payoff result else 0) ?_).trans
      (lazyRun_guess_payoff_le_forced environment computation memory budget hbudget payoff)
  intro result hr he
  have h := hevent result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
  simpa only [if_pos h.1] using h.2

end SphincsSecurity.Concrete.SecretGuessObservation
