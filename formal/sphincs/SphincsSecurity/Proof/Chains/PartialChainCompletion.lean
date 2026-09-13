import SphincsSecurity.Proof.Chains.PartialChainSuffix
import SphincsSecurity.Proof.Chains.AdaptiveChainQueryBound
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

def Extends {n : Nat} (before after : Fin n → State → Option State) : Prop :=
  ∀ step input answer, before step input = some answer → after step input = some answer

omit [Fintype State] [DecidableEq State] in
theorem Extends.tail {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.tail before) (Fin.tail after) := fun step input answer => h step.succ input answer

omit [Fintype State] [DecidableEq State] in
theorem knownRun_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (start endpoint : State) (hknown : knownRun before start = some endpoint) : knownRun after start = some endpoint := by
  induction n generalizing start with
  | zero => exact hknown
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at hknown ⊢
      obtain ⟨value, hvalue, hknown⟩ := hknown
      exact ⟨value, h 0 start value hvalue, ih h.tail value hknown⟩

theorem knownCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) (endpoint : State) :
    knownCount before endpoint ≤ knownCount after endpoint := by
  apply Finset.sum_le_sum
  intro start _
  by_cases hknown : knownRun before start = some endpoint
  · simp only [if_pos hknown, if_pos (knownRun_mono h start endpoint hknown), le_refl]
  · simp only [if_neg hknown, Nat.zero_le]

noncomputable def targetCount : {n : Nat} → (Fin n → State → Option State) → State → Nat
  | 0, _, _ => 0
  | _ + 1, observed, endpoint => knownCount observed endpoint + targetCount (Fin.tail observed) endpoint

noncomputable def completedCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  ∑ endpoint : State, targetCount observed endpoint

noncomputable def pendingCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  queryCount observed - completedCount observed

theorem suffixCount_eq_targetCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    knownCount observed endpoint + properSuffixCount observed endpoint = 1 + targetCount observed endpoint := by
  induction n with
  | zero => simp only [knownCount_empty, properSuffixCount, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [properSuffixCount, targetCount, ih]
      omega

theorem targetCount_eq_zero_of_no_contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : targetCount observed endpoint = 0 := by
  have hbound := suffixCount_le_one_of_no_contact observed endpoint h
  rw [suffixCount_eq_targetCount] at hbound
  omega

theorem targetCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) (endpoint : State) :
    targetCount before endpoint ≤ targetCount after endpoint := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact Nat.add_le_add (knownCount_mono h endpoint) (ih h.tail)

theorem completedCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    completedCount before ≤ completedCount after :=
  Finset.sum_le_sum fun endpoint _ => targetCount_mono h endpoint

omit [DecidableEq State] in
theorem queriedCount_eq_sum (observed : State → Option State) :
    queriedCount observed = ∑ input : State, if observed input = none then 0 else 1 := by
  rw [queriedCount, unqueried, Finset.card_filter]
  have hsplit : (∑ input : State, if observed input = none then 1 else 0) +
      (∑ input : State, if observed input = none then 0 else 1) = Fintype.card State := by
    rw [← Finset.sum_add_distrib]
    simp only [ite_add_ite, Nat.add_zero, Nat.zero_add, ite_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

theorem knownCount_sum {n : Nat} (observed : Fin n → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = ∑ start : State, if (knownRun observed start).isSome then 1 else 0 := by
  simp only [knownCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro start _
  cases knownRun observed start <;> simp

theorem knownCount_sum_le_queried {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) ≤ queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro start _
  cases hrow : observed 0 start with
  | none => simp [knownRun, hrow]
  | some value =>
      simp only [reduceCtorEq, if_false]
      split <;> omega

theorem completedCount_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    completedCount observed ≤ queryCount observed := by
  induction n with
  | zero => simp [completedCount, targetCount, queryCount]
  | succ n ih =>
      simp only [completedCount, targetCount, Finset.sum_add_distrib, queryCount, Fin.sum_univ_succ]
      exact Nat.add_le_add (knownCount_sum_le_queried observed) (ih (Fin.tail observed))

theorem pendingCount_partition {n : Nat} (observed : Fin n → State → Option State) :
    pendingCount observed + completedCount observed = queryCount observed :=
  Nat.sub_add_cancel (completedCount_le_queryCount observed)

omit [Fintype State] in
theorem record_extends {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    Extends observed (record observed query answer) := by
  intro step input old hold
  by_cases hstep : step = query.1
  · subst step
    by_cases hinput : input = query.2
    · subst input
      have heq : old = answer := by rcases hconsistent with h | h <;> simp_all
      simp [record, heq]
    · simpa only [record, Function.update_self, Function.update_of_ne hinput] using hold
  · simpa only [record, Function.update_of_ne hstep] using hold

theorem pendingCount_record_le {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    pendingCount (record observed query answer) ≤ pendingCount observed + 1 := by
  have hbefore := pendingCount_partition observed
  have hafter := pendingCount_partition (record observed query answer)
  have htotal := queryCount_record_le observed query answer
  have hdone := completedCount_mono (record_extends observed query answer hconsistent)
  omega

theorem completedCount_add_target_le {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (endpoint : State) (hcontact : ¬Contact before endpoint) :
    completedCount before + targetCount after endpoint ≤ completedCount after := by
  have hzero := targetCount_eq_zero_of_no_contact before endpoint hcontact
  have hrest := Finset.sum_le_sum (s := Finset.univ.erase endpoint) fun other _ => targetCount_mono h other
  rw [completedCount, completedCount,
    ← Finset.add_sum_erase Finset.univ (fun other => targetCount before other) (Finset.mem_univ endpoint),
    ← Finset.add_sum_erase Finset.univ (fun other => targetCount after other) (Finset.mem_univ endpoint), hzero]
  omega

theorem first_contact_density_charge [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer endpoint : State) (hcontact : ¬Contact observed endpoint)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    meanPreimages (record observed query answer) endpoint + (pendingCount (record observed query answer) : ENNReal) ≤
      (pendingCount observed + 2 : Nat) := by
  have hbefore := pendingCount_partition observed
  have hafter := pendingCount_partition (record observed query answer)
  have htotal := queryCount_record_le observed query answer
  have hdone := completedCount_add_target_le (record_extends observed query answer hconsistent) endpoint hcontact
  have hcount : 1 + targetCount (record observed query answer) endpoint + pendingCount (record observed query answer) ≤
      pendingCount observed + 2 := by omega
  have hdensity := meanPreimages_le_suffixCount (record observed query answer) endpoint
  rw [suffixCount_eq_targetCount] at hdensity
  exact (_root_.add_le_add hdensity le_rfl).trans (by exact_mod_cast hcount)

end SphincsSecurity.Concrete.PartialChainEndpoint
