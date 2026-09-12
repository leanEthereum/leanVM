import SphincsSecurity.Proof.Chains.AdaptiveChainPotential
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

private theorem compensation_compose {a b c d e f : ENNReal} (hc : c ≠ ⊤)
    (hstep : a + d ≤ b + c) (htail : c + e ≤ d + f) : a + e ≤ b + f := by
  apply (ENNReal.add_le_add_iff_left hc).mp
  calc
    c + (a + e) = a + (c + e) := by ac_rfl
    _ ≤ a + (d + f) := _root_.add_le_add le_rfl htail
    _ = (a + d) + f := by rw [add_assoc]
    _ ≤ (b + c) + f := _root_.add_le_add hstep le_rfl
    _ = c + (b + f) := by ac_rfl

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem lazyRun_compensation (auxiliary : QueryImpl auxSpec PMF)
    (charge weight : Nat → (Fin n → State → Option State) → ENNReal)
    (hfinite : ∀ input observed spent,
      (∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2) ≠ ⊤)
    (hstep : ∀ input observed spent,
      charge spent observed + (∑' output, (lazyImpl auxiliary input).run observed output *
        weight (spent + if IsPrefixQuery input then 1 else 0) output.2) ≤
      weight spent observed + ∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (spent : Nat) :
    charge spent observed + (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      weight (spent + result.1.2) result.2) ≤
    weight spent observed + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      charge (spent + result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing observed spent with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.add_zero]
      exact le_of_eq (add_comm _ _)
  | query_bind input next ih =>
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, ← Nat.add_assoc]
      apply compensation_compose (hfinite input observed spent) (hstep input observed spent)
      have h := ENNReal.tsum_le_tsum fun output => mul_le_mul' (le_refl ((lazyImpl auxiliary input).run observed output))
        (ih output.1 output.2 (spent + if IsPrefixQuery input then 1 else 0))
      simpa only [expectation_add] using h

end SphincsSecurity.Concrete.PartialChainEndpoint
