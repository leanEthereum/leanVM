import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.AdaptiveChainObservation
import SphincsSecurity.Proof.Chains.PartialChainLikelihoodLower
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectation_bind {First Second : Type} (prior : PMF First) (next : First → PMF Second)
    (payoff : Second → ENNReal) :
    (∑' result, prior.bind next result * payoff result) =
      ∑' first, prior first * ∑' result, next first result * payoff result := by
  simpa only [PMF.probOutput_eq_apply, PMF.monad_bind_eq_bind] using
    tsum_probOutput_bind_mul prior next payoff

theorem expectation_map {First Second : Type} (prior : PMF First) (next : First → Second)
    (payoff : Second → ENNReal) :
    (∑' result, prior.map next result * payoff result) = ∑' first, prior first * payoff (next first) := by
  simpa only [PMF.probOutput_eq_apply, PMF.monad_map_eq_map] using
    tsum_probOutput_map_mul prior next payoff

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}

theorem run_weighted_payoff {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (payoff : Result × (Fin n → State → Option State) → ENNReal) :
    (∑' tables, completeTables observed tables * ∑' result, observedRun auxiliary tables computation observed result *
      ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff result)) =
        ∑' result, lazyRun auxiliary computation observed result * (meanPreimages result.2 endpoint * payoff result) := by
  have h := congrArg (fun law : PMF ((Fin n → State → State) × (Result × (Fin n → State → Option State))) =>
    ∑' result, law result * ((EndpointPreimageDensity.preimages evaluate result.1 endpoint : ENNReal) * payoff result.2))
    (run_posterior auxiliary computation observed)
  simp only [expectation_bind, expectation_map] at h
  rw [h]
  apply tsum_congr
  intro result
  congr 1
  simp only [meanPreimages, ← mul_assoc, ENNReal.tsum_mul_right]

theorem run_allocated_cost_lower {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (payoff : Result × (Fin n → State → Option State) → ENNReal) (budget : Nat)
    (hbudget : ∀ result ∈ (lazyRun auxiliary computation observed).support, queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, lazyRun auxiliary computation observed result * payoff result) ≤
      ∑' tables, completeTables observed tables * ∑' result, observedRun auxiliary tables computation observed result *
        ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff result) := by
  rw [run_weighted_payoff, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hzero : lazyRun auxiliary computation observed result = 0
  · simp only [hzero, zero_mul, mul_zero, le_refl]
  · have hlower := meanPreimages_ge_budget result.2 endpoint budget
      (hbudget result hzero)
    calc
      _ = lazyRun auxiliary computation observed result *
          ((1 - (budget : ENNReal) / Fintype.card State) * payoff result) := by ring
      _ ≤ _ := mul_le_mul_right (mul_le_mul_left hlower (payoff result)) _

end SphincsSecurity.Concrete.PartialChainEndpoint
