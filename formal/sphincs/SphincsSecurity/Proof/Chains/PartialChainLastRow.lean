import SphincsSecurity.Proof.Chains.PartialChainCompletion
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

omit [Fintype State] [DecidableEq State] in
theorem knownRun_isSome_eq_of_last {n : Nat} (before after : Fin n → State → Option State)
    (hearly : ∀ step input, step.val + 1 ≠ n → before step input = after step input)
    (hlast : ∀ step input, step.val + 1 = n → (before step input).isSome = (after step input).isSome)
    (start : State) : (knownRun before start).isSome = (knownRun after start).isSome := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero =>
          simpa [knownRun] using hlast 0 start rfl
      | succ n =>
          have hhead := hearly 0 start (by simp)
          have htail := ih (Fin.tail before) (Fin.tail after)
            (fun step input h => hearly step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ_ne_succ_iff] using h))
            (fun step input h => hlast step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ.injEq] using h))
          simp only [knownRun, hhead]
          cases after 0 start with
          | none => rfl
          | some value => exact htail value

theorem completedCount_eq_of_last {n : Nat} (before after : Fin n → State → Option State)
    (hearly : ∀ step input, step.val + 1 ≠ n → before step input = after step input)
    (hlast : ∀ step input, step.val + 1 = n → (before step input).isSome = (after step input).isSome) :
    completedCount before = completedCount after := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (∑ endpoint : State, (knownCount before endpoint + targetCount (Fin.tail before) endpoint)) =
        ∑ endpoint : State, (knownCount after endpoint + targetCount (Fin.tail after) endpoint)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, knownCount_sum, knownCount_sum]
      congr 1
      · exact Finset.sum_congr rfl fun start _ => congrArg (fun b : Bool => if b then 1 else 0)
          (knownRun_isSome_eq_of_last before after hearly hlast start)
      · exact ih (Fin.tail before) (Fin.tail after)
          (fun step input h => hearly step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ_ne_succ_iff] using h))
          (fun step input h => hlast step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ.injEq] using h))

omit [Fintype State] in
theorem record_isSome_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (first second : State) (step : Fin n) (input : State) :
    (record observed query first step input).isSome = (record observed query second step input).isSome := by
  by_cases hs : step = query.1
  · subst step
    by_cases hi : input = query.2
    · subst input; simp [record]
    · simp only [record, Function.update_self, Function.update_of_ne hi]
  · simp only [record, Function.update_of_ne hs]

theorem queryCount_record_answer_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (first second : State) : queryCount (record observed query first) = queryCount (record observed query second) := by
  unfold queryCount
  apply Finset.sum_congr rfl
  intro step _
  rw [queriedCount_eq_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  have h := record_isSome_eq observed query first second step input
  cases hfirst : record observed query first step input <;> cases hsecond : record observed query second step input <;> simp_all

theorem pendingCount_record_last_answer_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (hlast : query.1.val + 1 = n) (first second : State) :
    pendingCount (record observed query first) = pendingCount (record observed query second) := by
  unfold pendingCount
  rw [queryCount_record_answer_eq observed query first second]
  congr 1
  apply completedCount_eq_of_last
  · intro step input hearly
    have hs : step ≠ query.1 := fun h => hearly (by simpa only [h] using hlast)
    simp only [record, Function.update_of_ne hs]
  · intro step input _
    exact record_isSome_eq observed query first second step input

omit [Fintype State] [DecidableEq State] in
theorem contact_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (endpoint : State) (hc : Contact before endpoint) : Contact after endpoint := by
  obtain ⟨step, hstep, input, hinput⟩ := hc
  exact ⟨step, hstep, input, h step input endpoint hinput⟩

omit [Fintype State] in
theorem contact_record_iff {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer endpoint : State) (hc : ¬Contact observed endpoint) :
    Contact (record observed query answer) endpoint ↔ query.1.val + 1 = n ∧ answer = endpoint := by
  constructor
  · rintro ⟨step, hstep, input, hinput⟩
    by_cases hs : step = query.1
    · subst step
      by_cases hi : input = query.2
      · subst input
        exact ⟨hstep, by simpa only [record, Function.update_self, Option.some.injEq] using hinput⟩
      · exact False.elim (hc ⟨query.1, hstep, input, by simpa only [record, Function.update_self, Function.update_of_ne hi] using hinput⟩)
    · exact False.elim (hc ⟨step, hstep, input, by simpa only [record, Function.update_of_ne hs] using hinput⟩)
  · rintro ⟨hlast, rfl⟩
    exact ⟨query.1, hlast, query.2, by simp only [record, Function.update_self]⟩

omit [Fintype State] in
theorem record_of_known {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer : State) (h : observed query.1 query.2 = some answer) : record observed query answer = observed := by
  simp only [record, ← h, Function.update_eq_self]

theorem meanPreimages_observe [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * meanPreimages (record observed query answer) endpoint) =
      meanPreimages observed endpoint := by
  simp only [meanPreimages, ← ENNReal.tsum_mul_left, ← mul_assoc, completeTables_observe_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp

end SphincsSecurity.Concrete.PartialChainEndpoint
