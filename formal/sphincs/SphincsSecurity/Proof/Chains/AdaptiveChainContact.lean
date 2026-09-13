import SphincsSecurity.Proof.Chains.AdaptiveChainPotential
import SphincsSecurity.Proof.Chains.PartialChainContactPotential
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem lazyRun_counted_expectation (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (payoff : Result × (Fin n → State → Option State) → ENNReal) :
    (∑' result, lazyRun auxiliary computation observed result * payoff result) =
      ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * payoff (result.1.1, result.2) := by
  have h := congrArg (fun law : PMF (Result × (Fin n → State → Option State)) => ∑' result, law result * payoff result)
    (lazyRun_map auxiliary (QueryCap.counted IsPrefixQuery computation) Prod.fst observed)
  simpa only [QueryCap.counted_forget, expectation_map] using h

theorem lazyRun_contactPotential_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (endpoint : State) :
    (∑' result, lazyRun auxiliary computation observed result * contactPotential result.2 endpoint) ≤
      contactPotential observed endpoint + (2 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  rw [lazyRun_counted_expectation]
  apply lazyRun_potential_le auxiliary (fun current => contactPotential current endpoint) (2 / Fintype.card State)
  intro input current
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one]
      exact contactPotential_observe_le current query endpoint

theorem realRun_contact_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) :
    Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * ∑' result, idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  rw [show Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] =
    (∑' result, realRun auxiliary computation (fun _ _ => none) result * (if Contact result.2.2 result.1 then 1 else 0)) by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realRun_expectation]
  calc
    _ ≤ ∑' result, idealRun auxiliary computation (fun _ _ => none) result * contactPotential result.2.2 result.1 :=
      ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (contactPotential_dominates result.2.2 result.1)
    _ ≤ _ := by
      simp only [idealRun, expectation_bind, expectation_map]
      rw [← expectation_scale]
      apply ENNReal.tsum_le_tsum
      intro endpoint
      apply mul_le_mul' le_rfl
      simpa only [contactPotential_empty, zero_add] using
        lazyRun_contactPotential_le (auxiliary endpoint) (computation endpoint) (fun _ _ => none) endpoint

end SphincsSecurity.Concrete.PartialChainEndpoint
