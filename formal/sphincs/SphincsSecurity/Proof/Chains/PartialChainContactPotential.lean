import SphincsSecurity.Proof.Chains.PartialChainLastRow
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

noncomputable def contactPotential {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  if Contact observed endpoint then meanPreimages observed endpoint else (pendingCount observed : ENNReal) / Fintype.card State

theorem contactPotential_dominates {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint * (if Contact observed endpoint then 1 else 0) ≤ contactPotential observed endpoint := by
  by_cases h : Contact observed endpoint <;> simp [contactPotential, h]

theorem contactPotential_empty {n : Nat} (endpoint : State) : contactPotential (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [contactPotential, Contact, pendingCount, queryCount_empty]

theorem contactPotential_observe_of_contact {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) (hc : Contact observed endpoint) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactPotential (record observed query answer) endpoint) =
      contactPotential observed endpoint := by
  rw [contactPotential, if_pos hc, ← meanPreimages_observe observed query endpoint]
  apply tsum_congr
  intro answer
  cases hrow : observed query.1 query.2 with
  | none =>
      rw [contactPotential, if_pos (contact_mono (record_extends observed query answer (Or.inl hrow)) endpoint hc)]
  | some value =>
      by_cases hanswer : answer = value
      · subst answer
        rw [contactPotential, if_pos (contact_mono (record_extends observed query value (Or.inr hrow)) endpoint hc)]
      · simp only [rowLaw, PMF.pure_apply, if_neg hanswer, zero_mul]

theorem contactPotential_observe_le {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactPotential (record observed query answer) endpoint) ≤
      contactPotential observed endpoint + 2 / Fintype.card State := by
  by_cases hc : Contact observed endpoint
  · rw [contactPotential_observe_of_contact observed query endpoint hc]
    exact _root_.le_add_of_nonneg_right bot_le
  cases hrow : observed query.1 query.2 with
  | some value =>
      simp only [rowLaw]
      have hpure := tsum_probOutput_pure_mul (m := PMF) value
        (fun answer => contactPotential (record observed query answer) endpoint)
      simp only [PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure, record_of_known observed query value hrow] at hpure
      rw [hpure]
      exact _root_.le_add_of_nonneg_right bot_le
  | none =>
      by_cases hlast : query.1.val + 1 = n
      · calc
          _ ≤ ∑' answer, rowLaw none answer *
              ((if answer = endpoint then meanPreimages (record observed query endpoint) endpoint else 0) +
                (pendingCount (record observed query endpoint) : ENNReal) / Fintype.card State) := by
            apply ENNReal.tsum_le_tsum
            intro answer
            apply mul_le_mul' le_rfl
            by_cases heq : answer = endpoint
            · subst answer
              rw [contactPotential, if_pos ((contact_record_iff observed query endpoint endpoint hc).mpr ⟨hlast, rfl⟩), if_pos rfl]
              exact _root_.le_add_of_nonneg_right bot_le
            · rw [contactPotential, if_neg (by simpa only [contact_record_iff observed query answer endpoint hc, hlast, true_and] using heq), if_neg heq, zero_add]
              rw [pendingCount_record_last_answer_eq observed query hlast answer endpoint]
          _ = (meanPreimages (record observed query endpoint) endpoint +
                (pendingCount (record observed query endpoint) : ENNReal)) / Fintype.card State := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, mul_ite, mul_zero, tsum_ite_eq]
            simp only [rowLaw, PMF.uniformOfFintype_apply, div_eq_mul_inv, mul_comm, mul_add]
          _ ≤ (pendingCount observed + 2 : Nat) / (Fintype.card State : ENNReal) := by
            simpa only [div_eq_mul_inv] using mul_le_mul'
              (first_contact_density_charge observed query endpoint endpoint hc (Or.inl hrow))
              (le_refl (Fintype.card State : ENNReal)⁻¹)
          _ = _ := by simp only [contactPotential, if_neg hc, Nat.cast_add, Nat.cast_ofNat, ENNReal.add_div]
      · calc
          _ ≤ ∑' answer, rowLaw none answer * ((pendingCount observed + 2 : Nat) / (Fintype.card State : ENNReal)) := by
            apply ENNReal.tsum_le_tsum
            intro answer
            apply mul_le_mul' le_rfl
            rw [contactPotential, if_neg (by simp only [contact_record_iff observed query answer endpoint hc, hlast, false_and, not_false_eq_true])]
            have hp : pendingCount (record observed query answer) ≤ pendingCount observed + 2 :=
              (pendingCount_record_le observed query answer (Or.inl hrow)).trans (by omega)
            simpa only [div_eq_mul_inv] using mul_le_mul' (show (pendingCount (record observed query answer) : ENNReal) ≤ (pendingCount observed + 2 : Nat) by exact_mod_cast hp)
              (le_refl (Fintype.card State : ENNReal)⁻¹)
          _ = _ := by
            simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, contactPotential, if_neg hc, Nat.cast_add, Nat.cast_ofNat, ENNReal.add_div]

end SphincsSecurity.Concrete.PartialChainEndpoint
