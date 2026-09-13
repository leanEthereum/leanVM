import SphincsSecurity.Proof.Chains.PartialChainContactCount
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

def TwoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Prop :=
  ∃ start middle, observed (Fin.last n).castSucc start = some middle ∧ observed (Fin.last (n + 1)) middle = some endpoint

omit [Fintype State] [DecidableEq State] in
theorem twoEdge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (hextends : Extends before after)
    (endpoint : State) (h : TwoEdge before endpoint) : TwoEdge after endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  exact ⟨start, middle, hextends _ _ _ hfirst, hextends _ _ _ hlast⟩

omit [Fintype State] [DecidableEq State] in
theorem twoEdge_tail {n : Nat} (observed : Fin (n + 3) → State → Option State) (endpoint : State)
    (h : TwoEdge (Fin.tail observed) endpoint) : TwoEdge observed endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  have hindex : (Fin.last n).castSucc.succ = (Fin.last (n + 1)).castSucc := by apply Fin.ext; rfl
  exact ⟨start, middle, by simpa only [Fin.tail, hindex] using hfirst, by simpa only [Fin.tail, Fin.succ_last] using hlast⟩

omit [Fintype State] [DecidableEq State] in
theorem knownRun_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : TwoEdge observed endpoint := by
  induction n generalizing start with
  | zero =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hfirst, hlast⟩ := h
      change (observed 1 middle).bind (fun value => some value) = some endpoint at hlast
      have hrow : observed 1 middle = some endpoint := by
        cases hrow : observed 1 middle <;> simpa only [hrow, Option.bind_none, Option.bind_some] using hlast
      exact ⟨start, middle, hfirst, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, htail⟩ := h
      exact twoEdge_tail observed endpoint (ih (Fin.tail observed) middle htail)

theorem knownCount_eq_zero_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_twoEdge observed start endpoint hrun))

theorem targetCount_eq_contactCount_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : targetCount observed endpoint = contactCount observed endpoint := by
  induction n with
  | zero =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add, targetCount, targetCount, Nat.add_zero,
        ← contactCount_single, contactCount_tail]
  | succ n ih =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add,
        ih (Fin.tail observed) (fun htail => h (twoEdge_tail observed endpoint htail)), contactCount_tail]

theorem meanPreimages_le_contactCount_of_no_twoEdge [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages observed endpoint ≤ (1 + contactCount observed endpoint : Nat) := by
  have hbound := meanPreimages_le_suffixCount observed endpoint
  rwa [suffixCount_eq_targetCount, targetCount_eq_contactCount_of_no_twoEdge observed endpoint h] at hbound

omit [Fintype State] in
theorem twoEdge_record_earlier {n : Nat} (observed : Fin (n + 2) → State → Option State) (query : Fin (n + 2) × State)
    (answer endpoint : State) (hfirst : (Fin.last n).castSucc ≠ query.1) (hlast : Fin.last (n + 1) ≠ query.1) :
    TwoEdge (record observed query answer) endpoint ↔ TwoEdge observed endpoint := by
  simp only [TwoEdge, record, Function.update_of_ne hfirst, Function.update_of_ne hlast]

omit [Fintype State] in
theorem twoEdge_record_last {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint ↔
      answer = endpoint ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  have hindex : (Fin.last n).castSucc ≠ Fin.last (n + 1) := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hfirst' : observed (Fin.last n).castSucc start = some middle := by
      simpa only [record, Function.update_of_ne hindex] using hfirst
    by_cases hm : middle = input
    · subst middle
      exact ⟨by simpa only [record, Function.update_self, Option.some.injEq] using hlast, start, hfirst'⟩
    · exact False.elim (h ⟨start, middle, hfirst', by simpa only [record, Function.update_self, Function.update_of_ne hm] using hlast⟩)
  · rintro ⟨rfl, start, hfirst⟩
    exact ⟨start, input, by simpa only [record, Function.update_of_ne hindex] using hfirst,
      by simp only [record, Function.update_self]⟩

omit [Fintype State] in
theorem twoEdge_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint ↔ observed (Fin.last (n + 1)) answer = some endpoint := by
  have hindex : Fin.last (n + 1) ≠ (Fin.last n).castSucc := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hlast' : observed (Fin.last (n + 1)) middle = some endpoint := by
      simpa only [record, Function.update_of_ne hindex] using hlast
    by_cases hs : start = input
    · subst start
      have hm : answer = middle := by simpa only [record, Function.update_self, Option.some.injEq] using hfirst
      simpa only [hm] using hlast'
    · exact False.elim (h ⟨start, middle, by simpa only [record, Function.update_self, Function.update_of_ne hs] using hfirst, hlast'⟩)
  · intro hlast
    exact ⟨input, answer, by simp only [record, Function.update_self], by simpa only [record, Function.update_of_ne hindex] using hlast⟩

theorem twoEdge_last_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    Pr[fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint |
      rowLaw (observed (Fin.last (n + 1)) input)] =
        if ∃ start, observed (Fin.last n).castSucc start = some input then 1 / (Fintype.card State : ENNReal) else 0 := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_last observed input _ endpoint h]
  by_cases hp : ∃ start, observed (Fin.last n).castSucc start = some input
  · simp only [hp, and_true, if_true, tsum_ite_eq, PMF.uniformOfFintype_apply, one_div]
  · simp only [hp, and_false, if_false, tsum_zero]

theorem twoEdge_penultimate_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    Pr[fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint |
      rowLaw (observed (Fin.last n).castSucc input)] = (contactCount observed endpoint : ENNReal) / Fintype.card State := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_penultimate observed input _ endpoint h, PMF.uniformOfFintype_apply, tsum_fintype,
    contactCount_succ, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]

end SphincsSecurity.Concrete.PartialChainEndpoint
