import SphincsSecurity.Proof.Chains.AdaptiveChainLikelihood
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

def knownRun : {n : Nat} → (Fin n → State → Option State) → State → Option State
  | 0, _, start => some start
  | _ + 1, observed, start => (observed 0 start).bind (knownRun (Fin.tail observed))

noncomputable def knownCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Nat :=
  ∑ start : State, if knownRun observed start = some endpoint then 1 else 0

noncomputable def knownMass {n : Nat} (prior : PMF State) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  ∑' start, prior start * if knownRun observed start = some endpoint then 1 else 0

noncomputable def properSuffixCount : {n : Nat} → (Fin n → State → Option State) → State → Nat
  | 0, _, _ => 0
  | _ + 1, observed, endpoint => knownCount (Fin.tail observed) endpoint + properSuffixCount (Fin.tail observed) endpoint

omit [Nonempty State] in
theorem knownCount_empty (observed : Fin 0 → State → Option State) (endpoint : State) : knownCount observed endpoint = 1 := by
  simp [knownCount, knownRun]

omit [Nonempty State] in
theorem knownMass_empty (prior : PMF State) (observed : Fin 0 → State → Option State) (endpoint : State) :
    knownMass prior observed endpoint = prior endpoint := by
  simp [knownMass, knownRun]

omit [Fintype State] [Nonempty State] in
theorem knownMass_pure {n : Nat} (value : State) (observed : Fin n → State → Option State) (endpoint : State) :
    knownMass (PMF.pure value) observed endpoint = if knownRun observed value = some endpoint then 1 else 0 := by
  simpa only [knownMass, PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure] using
    (tsum_probOutput_pure_mul (m := PMF) value (fun start => if knownRun observed start = some endpoint then 1 else 0))

theorem knownMass_uniform {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    knownMass (PMF.uniformOfFintype State) observed endpoint =
      (knownCount observed endpoint : ENNReal) / Fintype.card State := by
  rw [knownMass, tsum_fintype, knownCount, Nat.cast_sum]
  simp only [PMF.uniformOfFintype_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.mul_sum, mul_comm]

theorem advance_knownMass_le {n : Nat} (prior : PMF State) (observed : Fin (n + 1) → State → Option State) (endpoint : State) :
    knownMass (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed) endpoint ≤
      knownMass prior observed endpoint + (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := by
  rw [knownMass, expectation_bind]
  calc
    _ ≤ ∑' input, prior input *
        ((if knownRun observed input = some endpoint then 1 else 0) +
          (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State) := by
      apply ENNReal.tsum_le_tsum
      intro input
      apply mul_le_mul' le_rfl
      change knownMass (rowLaw (observed 0 input)) (Fin.tail observed) endpoint ≤ _
      cases hrow : observed 0 input with
      | none => simp only [rowLaw, knownMass_uniform, knownRun, hrow, Option.bind_none, reduceCtorEq, if_false, zero_add, le_refl]
      | some value =>
          simp only [rowLaw, knownMass_pure, knownRun, hrow, Option.bind_some]
          exact _root_.le_add_of_nonneg_right bot_le
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, knownMass]

theorem kernel_le_knownMass {n : Nat} (prior : PMF State) (observed : Fin n → State → Option State) (endpoint : State) :
    prior.bind (kernel observed) endpoint ≤
      knownMass prior observed endpoint + (properSuffixCount observed endpoint : ENNReal) / Fintype.card State := by
  induction n generalizing prior with
  | zero => simp [kernel, knownMass_empty, properSuffixCount]
  | succ n ih =>
      have h := ih (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed)
      have hstep := advance_knownMass_le prior observed endpoint
      calc
        _ ≤ knownMass (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed) endpoint +
            (properSuffixCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := by
          simpa only [kernel, PMF.bind_bind] using h
        _ ≤ (knownMass prior observed endpoint + (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State) +
            (properSuffixCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := _root_.add_le_add hstep le_rfl
        _ = _ := by rw [properSuffixCount, Nat.cast_add, ENNReal.add_div, add_assoc]

theorem meanPreimages_le_suffixCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint ≤ (knownCount observed endpoint + properSuffixCount observed endpoint : Nat) := by
  rw [meanPreimages_eq]
  have h := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) (kernel_le_knownMass (PMF.uniformOfFintype State) observed endpoint)
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [knownMass_uniform, Nat.cast_add, div_eq_mul_inv, mul_add, mul_left_comm (Fintype.card State : ENNReal),
    ENNReal.mul_inv_cancel hcard (by finiteness), mul_one] using h

def Contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Prop :=
  ∃ step : Fin n, step.val + 1 = n ∧ ∃ input, observed step input = some endpoint

omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem contact_tail {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State)
    (h : Contact (Fin.tail observed) endpoint) : Contact observed endpoint := by
  obtain ⟨step, hstep, input, hinput⟩ := h
  exact ⟨step.succ, by simpa only [Fin.val_succ] using congrArg Nat.succ hstep, input, hinput⟩

omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem knownRun_contact {n : Nat} (observed : Fin (n + 1) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : Contact observed endpoint := by
  induction n generalizing start with
  | zero =>
      have hrow : observed 0 start = some endpoint := by
        cases hstart : observed 0 start <;> simpa only [knownRun, hstart, Option.bind_none, Option.bind_some] using h
      exact ⟨0, rfl, start, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨value, _, hvalue⟩ := h
      exact contact_tail observed endpoint (ih (Fin.tail observed) value hvalue)

omit [Nonempty State] in
theorem knownCount_eq_zero_of_no_contact {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_contact observed start endpoint hrun))

omit [Nonempty State] in
theorem suffixCount_le_one_of_no_contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : knownCount observed endpoint + properSuffixCount observed endpoint ≤ 1 := by
  induction n with
  | zero => simp only [knownCount_empty, properSuffixCount, Nat.add_zero, le_refl]
  | succ n ih =>
      rw [knownCount_eq_zero_of_no_contact observed endpoint h, properSuffixCount, Nat.zero_add]
      exact ih (Fin.tail observed) (fun htail => h (contact_tail observed endpoint htail))

end SphincsSecurity.Concrete.PartialChainEndpoint
