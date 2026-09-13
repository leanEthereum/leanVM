import SphincsSecurity.Proof.Chains.PartialChainRowCharge
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

noncomputable def longCompleted : {n : Nat} → (Fin n → State → Option State) → Nat
  | 0, _ => 0
  | 1, _ => 0
  | _ + 2, observed => (∑ endpoint : State, knownCount observed endpoint) + longCompleted (Fin.tail observed)

omit [Fintype State] [DecidableEq State] in
theorem Extends.init {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.init before) (Fin.init after) := fun step input answer => h step.castSucc input answer

theorem longCompleted_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    longCompleted before ≤ longCompleted after := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      cases n with
      | zero => exact le_rfl
      | succ n =>
          exact Nat.add_le_add (Finset.sum_le_sum fun endpoint _ => knownCount_mono h endpoint) (ih h.tail)

theorem knownCount_sum_single (observed : Fin 1 → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]

theorem completedCount_eq_longCompleted {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    completedCount observed = longCompleted observed + queriedCount (observed (Fin.last n)) := by
  induction n with
  | zero =>
      simp only [completedCount, targetCount, Nat.add_zero, longCompleted, Nat.zero_add]
      exact knownCount_sum_single observed
  | succ n ih =>
      change (∑ endpoint : State, (knownCount observed endpoint + targetCount (Fin.tail observed) endpoint)) = _
      rw [Finset.sum_add_distrib]
      change (∑ endpoint : State, knownCount observed endpoint) + completedCount (Fin.tail observed) = _
      rw [ih (Fin.tail observed)]
      simp only [longCompleted, Fin.tail, Fin.succ_last, Nat.add_assoc]

omit [DecidableEq State] in
theorem queryCount_split_last {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    queryCount observed = queryCount (Fin.init observed) + queriedCount (observed (Fin.last n)) := by
  simp only [queryCount, Fin.sum_univ_castSucc, Fin.init]

theorem longCompleted_le_prefix_queries {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    longCompleted observed ≤ queryCount (Fin.init observed) := by
  have h := completedCount_le_queryCount observed
  rw [completedCount_eq_longCompleted, queryCount_split_last] at h
  omega

theorem longCompleted_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    longCompleted observed ≤ queryCount observed := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
      have h := longCompleted_le_prefix_queries observed
      rw [queryCount_split_last]
      omega

theorem longCompleted_empty {n : Nat} : longCompleted (fun (_ : Fin n) (_ : State) => none) = 0 := by
  have h := longCompleted_le_queryCount (fun (_ : Fin n) (_ : State) => none)
  rw [queryCount_empty] at h
  omega

omit [Fintype State] [DecidableEq State] in
theorem tail_snoc {n : Nat} (before : Fin (n + 1) → State → Option State) (last : State → Option State) :
    @Fin.tail (n + 1) (fun _ => State → Option State) (Fin.snoc before last) =
      (Fin.snoc (Fin.tail before) last : Fin (n + 1) → State → Option State) := by
  have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [hs, Fin.tail_cons]

omit [Fintype State] [DecidableEq State] in
theorem knownRun_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    knownRun (Fin.snoc before last) = fun start => (knownRun before start).bind last := by
  induction n with
  | zero => funext start; simp [knownRun, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, knownRun, Fin.cons_zero, Fin.tail_cons, ih]
      simp only [knownRun, Option.bind_assoc]

theorem knownCount_sum_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    (∑ endpoint : State, knownCount (Fin.snoc before (Function.update last input (some answer))) endpoint) =
      (∑ endpoint : State, knownCount (Fin.snoc before last) endpoint) + knownCount before input := by
  rw [knownCount_sum, knownCount_sum]
  simp only [knownCount, ← Finset.sum_add_distrib, knownRun_snoc]
  apply Finset.sum_congr rfl
  intro start _
  cases hrun : knownRun before start with
  | none => simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, if_false, reduceCtorEq, Nat.add_zero]
  | some value =>
      by_cases hv : value = input
      · subst value
        simp only [Option.bind_some, Function.update_self, hfresh, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, if_true, if_false, Nat.zero_add]
      · simp only [Option.bind_some, Function.update_of_ne hv, Option.some.injEq, if_neg hv, Nat.add_zero]

theorem longCompleted_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    longCompleted (Fin.snoc before (Function.update last input (some answer))) =
      longCompleted (Fin.snoc before last) + targetCount before input := by
  induction n with
  | zero => simp only [longCompleted, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [longCompleted, longCompleted, tail_snoc, tail_snoc, knownCount_sum_last_fresh before last input answer hfresh,
        ih (Fin.tail before), targetCount]
      omega

theorem longCompleted_record_last {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n) input = none) :
    longCompleted (record observed (Fin.last n, input) answer) =
      longCompleted observed + targetCount (Fin.init observed) input := by
  have h := longCompleted_last_fresh (Fin.init observed) (observed (Fin.last n)) input answer hfresh
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h

omit [Fintype State] in
theorem init_record {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (step : Fin n) (input answer : State) :
    Fin.init (record observed (step.castSucc, input) answer) = record (Fin.init observed) (step, input) answer := by
  simp only [record, Fin.init_update_castSucc, Fin.init]

theorem longCompleted_prefix_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    longCompleted (Fin.init (record observed ((Fin.last n).castSucc, input) answer)) =
      longCompleted (Fin.init observed) + targetCount (Fin.init (Fin.init observed)) input := by
  rw [init_record]
  exact longCompleted_record_last (Fin.init observed) input answer hfresh

end SphincsSecurity.Concrete.PartialChainEndpoint
