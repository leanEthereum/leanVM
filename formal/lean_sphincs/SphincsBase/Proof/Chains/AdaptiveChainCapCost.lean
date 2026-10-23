import SphincsBase.Proof.Chains.AdaptiveChainCap
namespace SphincsBase.QueryCap

open _root_.OracleComp OracleSpec ENNReal

def spent {Result : Type} (budget : Nat) (result : Option (Result × Nat)) : Nat :=
  result.elim 0 (fun finished => budget - finished.2)

end SphincsBase.QueryCap

namespace SphincsBase.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)

include hcharge hreal

theorem realRun_cap_count_payoff (payoff : Result × Nat → ENNReal) :
    (∑' result, realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        (fun _ _ => none) result * result.2.1.elim 0 (fun finished => payoff (finished.1, budget - finished.2))) =
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * payoff result.2.1 := by
  have h := congrArg (fun law : PMF (Option (Result × Nat)) => ∑' result, law result * result.elim 0 payoff)
    (realRun_cap_recover_count auxiliary computation cost budget hcharge hreal)
  simpa only [expectation_map, Option.elim_map, Option.elim_some, Function.comp_def] using h

theorem idealRun_cap_spent_lower :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
          (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal)) ≤
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  apply (realRun_empty_cost_lower auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
    (fun result => (QueryCap.spent budget result.2.1 : ENNReal))).trans_eq
  have h := realRun_cap_count_payoff auxiliary computation cost budget hcharge hreal (fun result => (result.2 : ENNReal))
  convert h using 1
  apply tsum_congr
  intro result
  congr 1
  cases result.2.1 <;> simp only [QueryCap.spent, Option.elim_none, Option.elim_some, Nat.cast_zero]

end SphincsBase.Concrete.PartialChainEndpoint
