import SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SphincsSecurity.Proof.Base.QueryCap
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem expectation_pure {Result : Type} (result : Result) (payoff : Result → ENNReal) :
    (∑' output, PMF.pure result output * payoff output) = payoff result := by
  simpa only [PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure] using
    tsum_probOutput_pure_mul (m := PMF) result payoff

theorem expectation_add {Result : Type} (law : PMF Result) (first second : Result → ENNReal) :
    (∑' result, law result * (first result + second result)) =
      (∑' result, law result * first result) + ∑' result, law result * second result := by
  simp only [mul_add, ENNReal.tsum_add]

theorem expectation_scale {Result : Type} (law : PMF Result) (factor : ENNReal) (payoff : Result → ENNReal) :
    (∑' result, law result * (factor * payoff result)) = factor * ∑' result, law result * payoff result := by
  simp only [mul_left_comm _ factor, ENNReal.tsum_mul_left]

theorem expectation_const {Result : Type} (law : PMF Result) (value : ENNReal) :
    (∑' result, law result * value) = value := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}

theorem lazyRun_map (auxiliary : QueryImpl auxSpec PMF) (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (f : Result → Next) (observed : Fin n → State → Option State) :
    lazyRun auxiliary (f <$> computation) observed = (lazyRun auxiliary computation observed).map (fun result => (f result.1, result.2)) := by
  simp only [lazyRun, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map]

theorem lazyRun_potential_le (auxiliary : QueryImpl auxSpec PMF)
    (potential : (Fin n → State → Option State) → ENNReal) (rate : ENNReal)
    (hstep : ∀ input observed,
      (∑' result, (lazyImpl auxiliary input).run observed result * potential result.2) ≤
        potential observed + rate * ((if IsPrefixQuery input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * potential result.2) ≤
      potential observed + rate *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure result => simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | query_bind input next ih =>
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, Nat.cast_add, expectation_add, expectation_const]
      calc
        _ ≤ ∑' output, (lazyImpl auxiliary input).run observed output *
            (potential output.2 + rate * ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result *
              (result.1.2 : ENNReal)) := ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (ih output.1 output.2)
        _ = (∑' output, (lazyImpl auxiliary input).run observed output * potential output.2) +
            rate * ∑' output, (lazyImpl auxiliary input).run observed output *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal) := by
          rw [expectation_add, expectation_scale]
        _ ≤ _ := by
          rw [mul_add, ← add_assoc]
          exact _root_.add_le_add (hstep input observed) le_rfl

end SphincsSecurity.Concrete.PartialChainEndpoint
