import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.AdaptiveChainLikelihood
import SphincsSecurity.Proof.Chains.AdaptiveChainQueryBound
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

noncomputable def realRun (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) : PMF (State × (Result × (Fin n → State → Option State))) :=
  (EndpointPreimageDensity.real (completeTables observed) evaluate).bind (fun pair =>
    (observedRun (auxiliary pair.2) pair.1 (computation pair.2) observed).map (fun result => (pair.2, result)))

noncomputable def idealRun (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) : PMF (State × (Result × (Fin n → State → Option State))) :=
  (PMF.uniformOfFintype State).bind (fun endpoint =>
    (lazyRun (auxiliary endpoint) (computation endpoint) observed).map (fun result => (endpoint, result)))

theorem realRun_expectation (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (payoff : State × (Result × (Fin n → State → Option State)) → ENNReal) :
    (∑' result, realRun auxiliary computation observed result * payoff result) =
      ∑' result, idealRun auxiliary computation observed result *
        (meanPreimages result.2.2 result.1 * payoff result) := by
  classical
  letI : DecidableEq (Fin n → State → State) := Classical.decEq _
  simp only [realRun, expectation_bind, expectation_map]
  rw [EndpointPreimageDensity.real_payoff, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [EndpointPreimageDensity.ideal_apply, div_eq_mul_inv]
  simp only [idealRun, expectation_bind, expectation_map, PMF.uniformOfFintype_apply]
  apply tsum_congr
  intro endpoint
  rw [← run_weighted_payoff (auxiliary endpoint) (computation endpoint) observed endpoint
    (fun result => payoff (endpoint, result)), ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro tables
  have hfactor :
      (∑' result, observedRun (auxiliary endpoint) tables (computation endpoint) observed result *
        ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff (endpoint, result))) =
      (EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) *
        ∑' result, observedRun (auxiliary endpoint) tables (computation endpoint) observed result * payoff (endpoint, result) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro result
    ring
  rw [hfactor]
  ring

theorem idealRun_queryCount_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (result : State × (Result × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary computation observed).support) :
    queryCount result.2.2 ≤ queryCount observed + budget := by
  rw [idealRun, PMF.mem_support_bind_iff] at hresult
  obtain ⟨endpoint, _, hresult⟩ := hresult
  rw [PMF.mem_support_map_iff] at hresult
  obtain ⟨output, houtput, rfl⟩ := hresult
  exact lazyRun_queryCount_le (auxiliary endpoint) (computation endpoint) observed budget (hbound endpoint) output houtput

theorem realRun_cost_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (payoff : State × (Result × (Fin n → State → Option State)) → ENNReal) :
    (1 - ((queryCount observed + budget : Nat) : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary computation observed result * payoff result) ≤
      ∑' result, realRun auxiliary computation observed result * payoff result := by
  rw [realRun_expectation, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hzero : idealRun auxiliary computation observed result = 0
  · simp only [hzero, zero_mul, mul_zero, le_refl]
  · have hlower := meanPreimages_ge_budget result.2.2 result.1 (queryCount observed + budget)
      (idealRun_queryCount_le auxiliary computation observed budget hbound result hzero)
    calc
      _ = idealRun auxiliary computation observed result *
          ((1 - ((queryCount observed + budget : Nat) : ENNReal) / Fintype.card State) * payoff result) := by ring
      _ ≤ _ := mul_le_mul_right (mul_le_mul_left hlower (payoff result)) _

theorem realRun_empty_cost_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (payoff : State × (Result × (Fin n → State → Option State)) → ENNReal) :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary computation (fun _ _ => none) result * payoff result) ≤
      ∑' result, realRun auxiliary computation (fun _ _ => none) result * payoff result := by
  simpa only [queryCount_empty, zero_add] using
    realRun_cost_lower auxiliary computation (fun _ _ => none) budget hbound payoff

end SphincsSecurity.Concrete.PartialChainEndpoint
