import SphincsSecurity.Proof.Chains.PartialChainTwoEdgeCompensation
import SphincsSecurity.Proof.Chains.AdaptiveChainCompensation
import SphincsSecurity.Proof.Chains.AdaptiveChainCountedRows
import SphincsSecurity.Proof.Chains.AdaptiveChainContactMoments
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem lazyRun_twoEdge_compensation (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (observed : Fin (n + 2) → State → Option State) (spent : Nat) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * twoEdgeWeight result.2 endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        ((twoEdgeCharge (spent + result.1.2) result.2 endpoint : ENNReal) / Fintype.card State) := by
  apply lazyRun_compensation auxiliary (fun used current => (twoEdgeCharge used current endpoint : ENNReal) / Fintype.card State)
    (fun _ current => twoEdgeWeight current endpoint) ?_ ?_ computation observed spent
  · intro input current used
    have hn : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        change (∑' answer : State, rowLaw (current query.1 query.2) answer *
          ((twoEdgeCharge (used + 1) (record current query answer) endpoint : ENNReal) / Fintype.card State)) ≠ ⊤
        rw [tsum_fintype]
        apply ENNReal.sum_ne_top.mpr
        intro answer _
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) (PMF.coe_le_one _ _))
          (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn)
  · intro input current used
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact le_of_eq (add_comm _ _)
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        exact twoEdge_observe_compensation used current query endpoint

omit [Nonempty State] in
theorem twoEdgeCharge_div_le (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ spent) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ((3 / 2 : ENNReal) / Fintype.card State) * (spent : ENNReal) +
        ((budget : ENNReal) / Fintype.card State) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
  have hdouble : 2 * (twoEdgeCharge spent observed endpoint : ENNReal) ≤ 3 * (spent : ENNReal) +
      2 * (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    exact_mod_cast (twoEdgeCharge_twice_le spent budget observed endpoint hs (hq.trans hs)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hq) _)
  have hcast : (twoEdgeCharge spent observed endpoint : ENNReal) ≤ (3 / 2 : ENNReal) * (spent : ENNReal) +
      (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp
    have ht : (3 / 2 : ENNReal) * 2 = 3 := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
    calc
      _ = 2 * (twoEdgeCharge spent observed endpoint : ENNReal) := mul_comm _ _
      _ ≤ _ := hdouble
      _ = (3 / 2 * 2) * (spent : ENNReal) + 2 * (budget : ENNReal) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by rw [ht]
      _ = _ := by ring
  have h := mul_le_mul' hcast (le_refl (Fintype.card State : ENNReal)⁻¹)
  simpa only [div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using h

theorem lazyRun_empty_twoEdge_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary computation (fun _ _ => none) result * twoEdgeWeight result.2 endpoint) ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  rw [lazyRun_counted_expectation]
  have hc := lazyRun_twoEdge_compensation auxiliary computation (fun _ _ => none) 0 endpoint
  simp only [twoEdgeCharge_empty, Nat.cast_zero, div_eq_mul_inv, zero_mul, twoEdgeWeight_empty, zero_add] at hc
  apply hc.trans
  calc
    _ ≤ ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (((3 / 2 : ENNReal) / Fintype.card State) * (result.1.2 : ENNReal) +
          ((budget : ENNReal) / Fintype.card State) *
            ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none)).support
      · apply mul_le_mul' le_rfl
        have hq := lazyRun_counted_queryCount_le auxiliary computation (fun _ _ => none) result hr
        simp only [queryCount_empty, Nat.zero_add] at hq
        exact twoEdgeCharge_div_le result.1.2 budget result.2 endpoint (lazyRun_counted_budget_le auxiliary computation _ budget hbound result hr) hq
      · have hz : lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by rw [expectation_add, expectation_scale, expectation_scale]
    _ ≤ _ := by
      have h := _root_.add_le_add
        (le_refl (((3 / 2 : ENNReal) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal)))
        (lazyRun_empty_contact_correction auxiliary computation endpoint budget hbound)
      apply h.trans_eq
      simp only [div_eq_mul_inv]
      ring

theorem realRun_twoEdge_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
            (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  rw [show Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] =
      (∑' result, realRun auxiliary computation (fun _ _ => none) result * (if TwoEdge result.2.2 result.1 then 1 else 0)) by
        simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realRun_expectation]
  simp only [idealRun, expectation_bind, expectation_map]
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro endpoint
  apply mul_le_mul' le_rfl
  exact lazyRun_empty_twoEdge_le (auxiliary endpoint) (computation endpoint) endpoint budget (hbound endpoint)

end SphincsSecurity.Concrete.PartialChainEndpoint
