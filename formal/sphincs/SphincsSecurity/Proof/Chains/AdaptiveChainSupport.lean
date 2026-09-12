import SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_empty_apply_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (result : State × (Result × (Fin n → State → Option State))) :
    (1 - (budget : ENNReal) / Fintype.card State) * idealRun auxiliary computation (fun _ _ => none) result ≤
      realRun auxiliary computation (fun _ _ => none) result := by
  classical
  have h := realRun_empty_cost_lower auxiliary computation budget hbound (fun output => if output = result then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, tsum_ite_eq] using h

theorem idealRun_empty_support_subset (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (hsmall : budget < Fintype.card State) :
    (idealRun auxiliary computation (fun _ _ => none)).support ⊆
      (realRun auxiliary computation (fun _ _ => none)).support := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (budget : ENNReal) / Fintype.card State := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  intro result hresult
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpositive, pos_iff_ne_zero.mpr hresult⟩)
    (realRun_empty_apply_lower auxiliary computation budget hbound result))

end SphincsSecurity.Concrete.PartialChainEndpoint
