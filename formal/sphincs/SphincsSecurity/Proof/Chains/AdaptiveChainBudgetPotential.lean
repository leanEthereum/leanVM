import SphincsSecurity.Proof.Chains.AdaptiveChainPotential
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem lazyRun_budget_potential_le (auxiliary : QueryImpl auxSpec PMF)
    (potential : Nat → (Fin n → State → Option State) → ENNReal)
    (terminal : (Fin n → State → Option State) → ENNReal) (rate : ENNReal) (limit : Nat)
    (hterminal : ∀ budget observed, terminal observed ≤ potential budget observed)
    (hstep : ∀ input observed budget, budget ≤ limit → (¬IsPrefixQuery input ∨ 0 < budget) →
      (∑' result, (lazyImpl auxiliary input).run observed result *
        potential (if IsPrefixQuery input then budget - 1 else budget) result.2) ≤
          potential budget observed + rate * ((if IsPrefixQuery input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbudget : budget ≤ limit) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * terminal result.2) ≤
      potential budget observed + rate *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.cast_zero, mul_zero, add_zero]
      exact hterminal budget observed
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hremaining : (if IsPrefixQuery input then budget - 1 else budget) ≤ limit := by split <;> omega
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, Nat.cast_add, expectation_add, expectation_const]
      calc
        _ ≤ ∑' output, (lazyImpl auxiliary input).run observed output *
            (potential (if IsPrefixQuery input then budget - 1 else budget) output.2 + rate *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal)) :=
          ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl
            (ih output.1 output.2 _ hremaining (hbound.2 output.1))
        _ = (∑' output, (lazyImpl auxiliary input).run observed output *
              potential (if IsPrefixQuery input then budget - 1 else budget) output.2) +
            rate * ∑' output, (lazyImpl auxiliary input).run observed output *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal) := by
          rw [expectation_add, expectation_scale]
        _ ≤ _ := by
          rw [mul_add, ← add_assoc]
          exact _root_.add_le_add (hstep input observed budget hbudget hbound.1) le_rfl

end SphincsSecurity.Concrete.PartialChainEndpoint
