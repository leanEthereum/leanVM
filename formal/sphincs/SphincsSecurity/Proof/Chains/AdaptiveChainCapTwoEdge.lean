import SphincsSecurity.Proof.Chains.AdaptiveChainTwoEdge
import SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)

include hcharge hreal

theorem realRun_cap_twoEdge_eq :
    Pr[fun result => TwoEdge result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin (n + 2) → State → Option State))) =>
    Pr[fun result => TwoEdge result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem realRun_twoEdge_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_twoEdge_eq auxiliary computation cost budget hcharge hreal]
  have h := realRun_twoEdge_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
  rw [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h
  exact h

omit hcharge hreal in
def TwoEdgeEvent : {depth : Nat} → (Fin depth → State → Option State) → State → Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | _ + 2, observed, endpoint => TwoEdge observed endpoint

omit hcharge hreal in
theorem realRun_twoEdgeEvent_le_cap_cost {depth : Nat} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec depth State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
      result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
  | succ depth =>
      cases depth with
      | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
      | succ depth => exact realRun_twoEdge_le_cap_cost auxiliary computation cost budget hcharge hreal hsmall

end SphincsSecurity.Concrete.PartialChainEndpoint
