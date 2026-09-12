import SphincsSecurity.Proof.Chains.PartialChainContactCount
import SphincsSecurity.Proof.Chains.AdaptiveChainBudgetPotential
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

noncomputable def contactMomentPotential (remaining : Nat) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  (contactFactorial (contactCount observed endpoint) : ENNReal) +
    (2 * remaining : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal)

theorem contactMomentPotential_observe_le (observed : Fin n → State → Option State) (query : Fin n × State)
    (endpoint : State) (remaining limit : Nat) (hremaining : remaining ≤ limit) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactMomentPotential remaining (record observed query answer) endpoint) ≤
      contactMomentPotential (remaining + 1) observed endpoint + (2 * limit : Nat) / (Fintype.card State : ENNReal)^2 := by
  simp only [contactMomentPotential, expectation_add, expectation_scale]
  calc
    _ ≤ ((contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal)) +
        ((2 * remaining : Nat) / (Fintype.card State : ENNReal)) *
          ((contactCount observed endpoint : ENNReal) + 1 / Fintype.card State) :=
      _root_.add_le_add (contactFactorial_observe_le observed query endpoint)
        (mul_le_mul' le_rfl (contactCount_observe_le observed query endpoint))
    _ = (contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * (remaining + 1) : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal) +
          (2 * remaining : Nat) / (Fintype.card State : ENNReal)^2 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, ENNReal.inv_pow]
      ring
    _ ≤ _ := by
      apply _root_.add_le_add le_rfl
      have h : (2 * remaining : Nat) ≤ 2 * limit := Nat.mul_le_mul_left 2 hremaining
      simpa only [div_eq_mul_inv] using mul_le_mul'
        (show ((2 * remaining : Nat) : ENNReal) ≤ (2 * limit : Nat) by exact_mod_cast h)
        (le_refl ((Fintype.card State : ENNReal)^2)⁻¹)

theorem lazyRun_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (contactCount result.2 endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + (1 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_potential_le auxiliary (fun current => (contactCount current endpoint : ENNReal)) (1 / Fintype.card State)
  intro input current
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one]
      exact contactCount_observe_le current query endpoint

theorem lazyRun_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      contactMomentPotential budget observed endpoint + ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_budget_potential_le auxiliary (fun remaining current => contactMomentPotential remaining current endpoint)
    (fun current => (contactFactorial (contactCount current endpoint) : ENNReal))
    ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) budget
    (fun _ _ => _root_.le_add_of_nonneg_right bot_le) ?_ computation observed budget le_rfl hbound
  intro input current remaining hremaining hpositive
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      have hpos : 0 < remaining := by simpa only [IsPrefixQuery, not_true_eq_false, false_or] using hpositive
      cases remaining with
      | zero => omega
      | succ remaining =>
          simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one, Nat.add_sub_cancel]
          exact contactMomentPotential_observe_le current query endpoint remaining budget (by omega)

theorem lazyRun_empty_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactCount result.2 endpoint : ENNReal)) ≤
      (1 / Fintype.card State) * ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (result.1.2 : ENNReal) := by
  simpa only [contactCount_empty, Nat.cast_zero, zero_add] using lazyRun_contactCount_le auxiliary computation (fun _ _ => none) endpoint

theorem lazyRun_empty_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simpa only [contactMomentPotential, contactCount_empty, contactFactorial, Nat.zero_mul, Nat.cast_zero, mul_zero, zero_add] using
    lazyRun_contactFactorial_le auxiliary computation (fun _ _ => none) endpoint budget hbound

theorem lazyRun_empty_contact_correction (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    ((budget : ENNReal) / Fintype.card State) *
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) ≤
      ((4 * ((budget : ENNReal) / Fintype.card State) + 2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, expectation_add, expectation_scale]
  have h := mul_le_mul' (le_refl ((budget : ENNReal) / Fintype.card State))
    (_root_.add_le_add (lazyRun_empty_contactFactorial_le auxiliary computation endpoint budget hbound)
      (mul_le_mul' (le_refl (4 : ENNReal)) (lazyRun_empty_contactCount_le auxiliary computation endpoint)))
  apply h.trans_eq
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  ring

end SphincsSecurity.Concrete.PartialChainEndpoint
