import SphincsSecurity.Proof.Chains.PartialChainLastRow
import SphincsSecurity.Proof.Chains.AdaptiveChainPotential
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

noncomputable def contactCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Nat :=
  ∑ query : Fin n × State, if query.1.val + 1 = n ∧ observed query.1 query.2 = some endpoint then 1 else 0

theorem contactCount_empty {n : Nat} (endpoint : State) : contactCount (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [contactCount]

theorem contactCount_succ {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State) :
    contactCount observed endpoint = ∑ input : State, if observed (Fin.last n) input = some endpoint then 1 else 0 := by
  rw [contactCount, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp only [Fin.val_last, true_and]
  · intro step _ hstep
    have hn : step.val + 1 ≠ n + 1 := by
      intro hn
      apply hstep
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    simp only [hn, false_and, if_false, Finset.sum_const_zero]
  · simp

theorem contactCount_tail {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) :
    contactCount (Fin.tail observed) endpoint = contactCount observed endpoint := by
  simp only [contactCount_succ, Fin.tail, Fin.succ_last]

theorem contactCount_single (observed : Fin 1 → State → Option State) (endpoint : State) :
    contactCount observed endpoint = knownCount observed endpoint := by
  rw [contactCount_succ, knownCount]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]

omit [Fintype State] in
theorem record_at_other {n : Nat} (observed : Fin n → State → Option State) (query other : Fin n × State)
    (answer : State) (h : other ≠ query) : record observed query answer other.1 other.2 = observed other.1 other.2 := by
  by_cases hs : other.1 = query.1
  · have hi : other.2 ≠ query.2 := fun heq => h (Prod.ext hs heq)
    simp only [record, hs, Function.update_self, Function.update_of_ne hi]
  · simp only [record, Function.update_of_ne hs]

theorem contactCount_record_fresh {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer endpoint : State) (hfresh : observed query.1 query.2 = none) :
    contactCount (record observed query answer) endpoint =
      contactCount observed endpoint + if query.1.val + 1 = n ∧ answer = endpoint then 1 else 0 := by
  have hfun : (fun other : Fin n × State =>
      if other.1.val + 1 = n ∧ record observed query answer other.1 other.2 = some endpoint then 1 else 0) =
      Function.update (fun other : Fin n × State => if other.1.val + 1 = n ∧ observed other.1 other.2 = some endpoint then 1 else 0)
        query (if query.1.val + 1 = n ∧ answer = endpoint then 1 else 0) := by
    funext other
    by_cases ho : other = query
    · subst other
      simp only [record, Function.update_self, Option.some.injEq]
    · simp only [record_at_other observed query other answer ho, Function.update_of_ne ho]
  rw [contactCount, hfun, Finset.sum_update_of_mem (Finset.mem_univ query), Finset.sdiff_singleton_eq_erase,
    contactCount, ← Finset.add_sum_erase Finset.univ
      (fun other : Fin n × State => if other.1.val + 1 = n ∧ observed other.1 other.2 = some endpoint then 1 else 0)
      (Finset.mem_univ query)]
  simp only [hfresh, reduceCtorEq, and_false, if_false, Nat.zero_add, Nat.add_comm]

theorem contactCount_observe_increment_le [Nonempty State] {n : Nat}
    (value increment : Nat → ENNReal) (hincrement : ∀ k, value (k + 1) = value k + increment k)
    (observed : Fin n → State → Option State) (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * value (contactCount (record observed query answer) endpoint)) ≤
      value (contactCount observed endpoint) + increment (contactCount observed endpoint) / Fintype.card State := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      exact _root_.le_add_of_nonneg_right bot_le
  | none =>
      simp only [rowLaw, contactCount_record_fresh observed query _ endpoint hrow]
      by_cases hlast : query.1.val + 1 = n
      · simp only [hlast, true_and]
        have hvalue (answer : State) : value (contactCount observed endpoint + if answer = endpoint then 1 else 0) =
            value (contactCount observed endpoint) + if answer = endpoint then increment (contactCount observed endpoint) else 0 := by
          by_cases heq : answer = endpoint <;> simp only [heq, if_true, if_false, hincrement, add_zero]
        simp only [hvalue, expectation_add, expectation_const]
        simp only [mul_ite, mul_zero, tsum_ite_eq, PMF.uniformOfFintype_apply]
        exact le_of_eq (by rw [div_eq_mul_inv, mul_comm])
      · simp only [hlast, false_and, if_false, Nat.add_zero, expectation_const]
        exact _root_.le_add_of_nonneg_right bot_le

theorem contactCount_observe_le [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * (contactCount (record observed query answer) endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + 1 / Fintype.card State :=
  contactCount_observe_increment_le (fun k => k) (fun _ => 1) (fun k => by simp only [Nat.cast_add, Nat.cast_one]) observed query endpoint

def contactFactorial (k : Nat) : Nat := k * (k - 1)

theorem contactFactorial_succ (k : Nat) : contactFactorial (k + 1) = contactFactorial k + 2 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring

theorem contactFactorial_observe_le [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * (contactFactorial (contactCount (record observed query answer) endpoint) : ENNReal)) ≤
      (contactFactorial (contactCount observed endpoint) : ENNReal) + (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal) :=
  contactCount_observe_increment_le (fun k => contactFactorial k) (fun k => (2 * k : Nat))
    (fun k => by rw [contactFactorial_succ, Nat.cast_add]) observed query endpoint

end SphincsSecurity.Concrete.PartialChainEndpoint
