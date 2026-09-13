import SphincsSecurity.Proof.Chains.AdaptiveChainContact
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem lazyRun_contact_charge (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (hc : ¬Contact observed endpoint) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      (meanPreimages result.2 endpoint * (if Contact result.2 endpoint then 1 else 0))) ≤
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        ((queryCount observed + 2 * result.1.2 : Nat) : ENNReal)) / Fintype.card State := by
  have h := lazyRun_contactPotential_le auxiliary computation observed endpoint
  rw [lazyRun_counted_expectation] at h
  have hinit : contactPotential observed endpoint ≤ (queryCount observed : ENNReal) / Fintype.card State := by
    rw [contactPotential, if_neg hc]
    have hp : pendingCount observed ≤ queryCount observed := Nat.sub_le _ _
    simpa only [div_eq_mul_inv] using mul_le_mul' (show (pendingCount observed : ENNReal) ≤ queryCount observed by exact_mod_cast hp)
      (le_refl (Fintype.card State : ENNReal)⁻¹)
  calc
    _ ≤ ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * contactPotential result.2 endpoint :=
      ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (contactPotential_dominates result.2 endpoint)
    _ ≤ (queryCount observed : ENNReal) / Fintype.card State + (2 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) :=
      h.trans (_root_.add_le_add hinit le_rfl)
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, expectation_add, expectation_const, expectation_scale, div_eq_mul_inv]
      ring

theorem run_contact_charge_transfer (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (hc : ¬Contact observed endpoint) (budget : Nat)
    (hbudget : ∀ result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed).support,
      queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        (meanPreimages result.2 endpoint * (if Contact result.2 endpoint then 1 else 0))) ≤
      ∑' tables, completeTables observed tables * ∑' result,
        observedRun auxiliary tables (QueryCap.counted IsPrefixQuery computation) observed result *
          ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) *
            ((queryCount observed + 2 * result.1.2 : Nat) : ENNReal)) := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcharge := mul_le_mul' (le_refl (Fintype.card State : ENNReal))
    (lazyRun_contact_charge auxiliary computation observed endpoint hc)
  simp only [div_eq_mul_inv, mul_left_comm (Fintype.card State : ENNReal),
    ENNReal.mul_inv_cancel hcard (by finiteness), mul_one] at hcharge
  apply (mul_le_mul' (le_refl (1 - (budget : ENNReal) / Fintype.card State)) hcharge).trans
  exact run_allocated_cost_lower auxiliary (QueryCap.counted IsPrefixQuery computation) observed endpoint
    (fun result => ((queryCount observed + 2 * result.1.2 : Nat) : ENNReal)) budget hbudget

end SphincsSecurity.Concrete.PartialChainEndpoint
