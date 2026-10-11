import Whir.PCSStateRestoration

/-! Adaptive first-registration metadata for the restoration theorem. Immutable
root tables and public prefixes are captured before the first requested draw;
they need not be encoded literally in the raw RO key. Reusing a raw key reuses
that capture. An actual-source adapter must justify this replay outside its
explicit Merkle/framing bad events; this file does not assert that justification. -/
namespace Whir.PCSStateRestoration.Adaptive
open TypedOracleCompiler TypedFiatShamirGame
open FiatShamirGame (average average_mono average_const average_add)

set_option autoImplicit false
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {Public : Type w}

structure Certificate (Key : Type u) (Answer : Key → Type v) (Public : Type w) where
  before : Public → Key → Bool
  after : Public → (key : Key) → Answer key → Bool

abbrev Entry (Key : Type u) (Answer : Key → Type v) (Public : Type w) := Public × Sigma Answer
abbrev History (Key : Type u) (Answer : Key → Type v) (Public : Type w) := List (Entry Key Answer Public)

structure View (Key : Type u) (Answer : Key → Type v) (Public : Type w) where
  history : History Key Answer Public
  registry : Key → Option Public

def initial : View Key Answer Public := ⟨[],fun _ => none⟩

structure Policy (Key : Type u) (Answer : Key → Type v) (Public : Type w) where
  choose : Nat → History Key Answer Public → Option Key
  prepare : Nat → History Key Answer Public → Key → Public

/-- This function consults completed registration metadata, never the pending
answer or a reference oracle. Registration is fixed before the queried draw. -/
def snapshot (policy : Policy Key Answer Public) (cursor : Nat)
    (view : View Key Answer Public) (key : Key) : Public :=
  match view.registry key with
  | some publicData => publicData
  | none => policy.prepare cursor view.history key

def Transition (cert : Certificate Key Answer Public) (publicData : Public)
    (key : Key) (answer : Answer key) : Prop :=
  cert.before publicData key = false ∧ cert.after publicData key answer = true

def Dirty (cert : Certificate Key Answer Public) (history : History Key Answer Public) : Prop :=
  ∃ entry ∈ history, Transition cert entry.1 entry.2.1 entry.2.2

def Doomed (cert : Certificate Key Answer Public) (history : History Key Answer Public) : Prop :=
  ∃ entry ∈ history, cert.after entry.1 entry.2.1 entry.2.2 = true

section Execution
variable [DecidableEq Key]

/-- Existing metadata survives exactly; only a previously absent entry is
inserted. Logging repeats preserves the complete adversarial past view. -/
def advanceCaptured (view : View Key Answer Public) (key : Key)
    (publicData : Public) (answer : Answer key) : View Key Answer Public :=
  ⟨(publicData,⟨key,answer⟩) :: view.history,
    if view.registry key = none then Function.update view.registry key (some publicData)
    else view.registry⟩

def advance (policy : Policy Key Answer Public) (cursor : Nat)
    (view : View Key Answer Public) (key : Key) (answer : Answer key) : View Key Answer Public :=
  advanceCaptured view key (snapshot policy cursor view key) answer

theorem registry_never_overwrites (policy : Policy Key Answer Public) (cursor : Nat)
    (view : View Key Answer Public) (key wanted : Key) (answer : Answer key) (publicData : Public)
    (registered : view.registry wanted = some publicData) :
    (advance policy cursor view key answer).registry wanted = some publicData := by
  by_cases same : wanted = key
  · subst wanted
    simp [advance,advanceCaptured,registered]
  · by_cases missing : view.registry key = none
    · simp [advance,advanceCaptured,missing,Function.update_of_ne same,registered]
    · simp [advance,advanceCaptured,missing,registered]

theorem registry_records_snapshot (policy : Policy Key Answer Public) (cursor : Nat)
    (view : View Key Answer Public) (key : Key) (answer : Answer key) :
    (advance policy cursor view key answer).registry key = some (snapshot policy cursor view key) := by
  cases registered : view.registry key with
  | none => simp [advance,advanceCaptured,registered]
  | some publicData => simp [advance,advanceCaptured,snapshot,registered]

omit [DecidableEq Key] in
theorem replay_snapshot (policy : Policy Key Answer Public) (cursor : Nat)
    (view : View Key Answer Public) (key : Key) (publicData : Public)
    (registered : view.registry key = some publicData) :
    snapshot policy cursor view key = publicData := by simp [snapshot,registered]

/-- Precise actual-source replay adapter condition. If a raw key aliases a new
logical context, its pending literal certificate must agree with the first
capture. Merkle/framing exclusions may establish this; they are not assumed
away or converted to fresh randomness by the finite-game theorem. -/
def ReplayCompatible (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (cursor : Nat) (view : View Key Answer Public) (key : Key) : Prop :=
  ∀ publicData, view.registry key = some publicData →
    cert.before publicData key = cert.before (policy.prepare cursor view.history key) key ∧
    ∀ answer : Answer key, cert.after publicData key answer =
      cert.after (policy.prepare cursor view.history key) key answer

omit [DecidableEq Key] in
theorem replay_certificate_agrees (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (cursor : Nat) (view : View Key Answer Public) (key : Key)
    (compatible : ReplayCompatible cert policy cursor view key) :
    cert.before (snapshot policy cursor view key) key =
      cert.before (policy.prepare cursor view.history key) key ∧
    ∀ answer : Answer key, cert.after (snapshot policy cursor view key) key answer =
      cert.after (policy.prepare cursor view.history key) key answer := by
  cases registered : view.registry key with
  | none => simp [snapshot,registered]
  | some publicData =>
    simpa only [snapshot,registered] using compatible publicData registered

def program (policy : Policy Key Answer Public) : (n : Nat) → Nat → View Key Answer Public →
    Sampling Key Answer (View Key Answer Public) n
  | 0, _, view => .ret view
  | n+1, cursor, view =>
    match policy.choose cursor view.history with
    | none => Sampling.pad (Nat.le_succ n) (program policy n (cursor+1) view)
    | some key =>
      let publicData := snapshot policy cursor view key
      .draw key (fun answer =>
        program policy n (cursor+1) (advanceCaptured view key publicData answer))

/-- Exact structural condition needed for restoring a nonzero public state:
it inherits a completed state-one record. It has no probabilistic hypothesis. -/
def Causal (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public) :
    (n : Nat) → Nat → View Key Answer Public → Prop
  | 0, _, _ => True
  | n+1, cursor, view =>
    match policy.choose cursor view.history with
    | none => Causal cert policy n (cursor+1) view
    | some key => (cert.before (snapshot policy cursor view key) key = true → Doomed cert view.history) ∧
        ∀ answer, Causal cert policy n (cursor+1) (advance policy cursor view key answer)

private theorem dirty_advance (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (cursor : Nat) (view : View Key Answer Public) (key : Key) (answer : Answer key) :
    Dirty cert (advance policy cursor view key answer).history ↔
      Transition cert (snapshot policy cursor view key) key answer ∨ Dirty cert view.history := by
  simp [advance,advanceCaptured,Dirty]

private theorem coherent_advance (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (cursor : Nat) (view : View Key Answer Public) (key : Key) (answer : Answer key)
    (initialCoherent : Doomed cert view.history → Dirty cert view.history)
    (restore : cert.before (snapshot policy cursor view key) key = true → Doomed cert view.history) :
    Doomed cert (advance policy cursor view key answer).history →
      Dirty cert (advance policy cursor view key answer).history := by
  intro doomed
  obtain ⟨entry,member,after⟩ := doomed
  rcases List.mem_cons.mp member with equal | member
  · subst entry
    cases before : cert.before (snapshot policy cursor view key) key with
    | false => exact (dirty_advance cert policy cursor view key answer).mpr (Or.inl ⟨before,after⟩)
    | true =>
      exact (dirty_advance cert policy cursor view key answer).mpr (Or.inr (initialCoherent (restore before)))
  · exact (dirty_advance cert policy cursor view key answer).mpr (Or.inr (initialCoherent ⟨entry,member,after⟩))

theorem execution_has_transition (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (n cursor : Nat) (view : View Key Answer Public) (causal : Causal cert policy n cursor view)
    (initialCoherent : Doomed cert view.history → Dirty cert view.history)
    (table : (key : Key) → Answer key) :
    Doomed cert (Sampling.eval table (program policy n cursor view)).history →
      Dirty cert (Sampling.eval table (program policy n cursor view)).history := by
  induction n generalizing cursor view with
  | zero => exact initialCoherent
  | succ n ih =>
    cases chosen : policy.choose cursor view.history with
    | none =>
      simp only [program,chosen,Sampling.eval_pad]
      exact ih _ _ (by simpa only [Causal,chosen] using causal) initialCoherent
    | some key =>
      have localCausal : (cert.before (snapshot policy cursor view key) key = true → Doomed cert view.history) ∧
          ∀ answer, Causal cert policy n (cursor+1) (advance policy cursor view key answer) := by
        simpa only [Causal,chosen] using causal
      simp only [program,chosen,Sampling.eval]
      exact ih _ _ (localCausal.2 _) (coherent_advance cert policy cursor view key _ initialCoherent localCausal.1)

end Execution

section Probability
variable [DecidableEq Key] [∀ key, Fintype (Answer key)] [∀ key, Nonempty (Answer key)]

def ConditionalHazard (cert : Certificate Key Answer Public) (epsilon : ℚ) : Prop :=
  ∀ publicData key, cert.before publicData key = false →
    average (fun answer : Answer key => if cert.after publicData key answer = true then (1 : ℚ) else 0) ≤ epsilon

/-- Operational cache/metadata invariant. It will be derived from the empty
view and cache, not supplied as a security assumption on the final experiment. -/
def Recorded (view : View Key Answer Public) (cache : Cache Key Answer) : Prop :=
  ∀ key answer, cache key = some answer → ∃ publicData,
    view.registry key = some publicData ∧ (publicData,⟨key,answer⟩) ∈ view.history

omit [∀ key, Fintype (Answer key)] [∀ key, Nonempty (Answer key)] in
private theorem recorded_advance (policy : Policy Key Answer Public) (cursor : Nat)
    (view : View Key Answer Public) (cache : Cache Key Answer) (recorded : Recorded view cache)
    (key : Key) (answer : Answer key) :
    Recorded (advance policy cursor view key answer) (put cache key answer) := by
  intro wanted value present
  by_cases same : wanted = key
  · subst wanted
    simp only [put_self,Option.some.injEq] at present
    subst value
    exact ⟨snapshot policy cursor view key,registry_records_snapshot policy cursor view key answer,List.mem_cons_self⟩
  · obtain ⟨publicData,registered,member⟩ := recorded wanted value (by simpa [put_other,same] using present)
    exact ⟨publicData,registry_never_overwrites policy cursor view key wanted answer publicData registered,
      List.mem_cons_of_mem _ member⟩


/-- Actual adaptive memoized probability bound with first-capture metadata.
Retries can use the full past; only a distinct fresh raw-key exposure is charged. -/
theorem memo_transition_bound (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard cert epsilon)
    (n cursor : Nat) (view : View Key Answer Public) (cache : Cache Key Answer)
    (recorded : Recorded view cache) (clean : ¬ Dirty cert view.history) :
    Sampling.expectation (fun result => if Dirty cert result.1.history then (1 : ℚ) else 0)
      (RawOracleCoupling.memo (program policy n cursor view) cache) ≤ (n : ℚ)*epsilon := by
  classical
  induction n generalizing cursor view cache with
  | zero => simp [program,RawOracleCoupling.memo,Sampling.expectation,clean]
  | succ n ih =>
    have increase : (n : ℚ)*epsilon ≤ ((n+1 : Nat) : ℚ)*epsilon :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) nonnegative
    cases chosen : policy.choose cursor view.history with
    | none =>
      simp only [program,chosen,memo_expectation_pad]
      exact (ih _ _ _ recorded clean).trans increase
    | some key =>
      cases hit : cache key with
      | some answer =>
        obtain ⟨publicData,registered,member⟩ := recorded key answer hit
        have repeated : ¬ Transition cert (snapshot policy cursor view key) key answer := by
          rw [replay_snapshot policy cursor view key publicData registered]
          exact fun transition => clean ⟨_,member,transition⟩
        have continued : ¬ Dirty cert (advance policy cursor view key answer).history := by
          rw [dirty_advance]; exact not_or.mpr ⟨repeated,clean⟩
        have oldRecorded : Recorded (advance policy cursor view key answer) cache := by
          intro wanted value present
          obtain ⟨publicData,registered,member⟩ := recorded wanted value present
          exact ⟨publicData,registry_never_overwrites policy cursor view key wanted answer publicData registered,
            List.mem_cons_of_mem _ member⟩
        simp only [program,chosen,RawOracleCoupling.memo,hit,Sampling.expectation_pad]
        exact (ih _ _ _ oldRecorded continued).trans increase
      | none =>
        simp only [program,chosen,RawOracleCoupling.memo,hit,Sampling.expectation]
        have fibers (answer : Answer key) :
            Sampling.expectation (fun result => if Dirty cert result.1.history then (1 : ℚ) else 0)
              (RawOracleCoupling.memo (program policy n (cursor+1) (advance policy cursor view key answer))
                (put cache key answer)) ≤
              (if Transition cert (snapshot policy cursor view key) key answer then 1 else 0) + (n : ℚ)*epsilon := by
          by_cases bad : Transition cert (snapshot policy cursor view key) key answer
          · have one := Sampling.expectation_le_one
              (fun result : View Key Answer Public × Cache Key Answer => if Dirty cert result.1.history then (1 : ℚ) else 0)
              (fun result => by split <;> norm_num)
              (RawOracleCoupling.memo (program policy n (cursor+1) (advance policy cursor view key answer))
                (put cache key answer))
            simpa only [bad,↓reduceIte] using one.trans
              (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) nonnegative))
          · have continued : ¬ Dirty cert (advance policy cursor view key answer).history := by
              rw [dirty_advance]; exact not_or.mpr ⟨bad,clean⟩
            simpa only [bad,↓reduceIte,zero_add] using
              ih _ _ _ (recorded_advance policy cursor view cache recorded key answer) continued
        have localBound : average (fun answer : Answer key =>
            if Transition cert (snapshot policy cursor view key) key answer then (1 : ℚ) else 0) ≤ epsilon := by
          cases before : cert.before (snapshot policy cursor view key) key with
          | false => simpa only [Transition,before,true_and] using hazard (snapshot policy cursor view key) key before
          | true => simpa [Transition,before,average_const] using nonnegative
        calc
          _ ≤ average (fun answer : Answer key =>
            (if Transition cert (snapshot policy cursor view key) key answer then (1 : ℚ) else 0) + (n : ℚ)*epsilon) := average_mono fibers
          _ ≤ epsilon + (n : ℚ)*epsilon := by
            rw [average_add,average_const]; exact add_le_add localBound le_rfl
          _ = ((n+1 : Nat) : ℚ)*epsilon := by push_cast; ring

omit [DecidableEq Key] [∀ key, Nonempty (Answer key)] in
theorem conditionalHazard_of_uniform (cert : Certificate Key Answer Public) (epsilon : ℚ)
    (fibers : ∀ publicData key, cert.before publicData key = false →
      Soundness.uniformProb (Finset.univ.filter fun answer : Answer key =>
        cert.after publicData key answer = true) ≤ epsilon) : ConditionalHazard cert epsilon := by
  classical
  intro publicData key before
  simpa only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using fibers publicData key before

/-- Conditional game after an explicitly represented fixed public prefix.
Existing answers and first-registration metadata are not charged again. -/
theorem fixed_prefix_failure_probability [Fintype Key]
    (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard cert epsilon)
    (n cursor : Nat) (view : View Key Answer Public) (cache : Cache Key Answer)
    (recorded : Recorded view cache) (clean : ¬ Dirty cert view.history)
    (initialCoherent : Doomed cert view.history → Dirty cert view.history)
    (causal : Causal cert policy n cursor view) (failure : View Key Answer Public → Prop)
    (endpoint : ∀ table : (key : Key) → Answer key,
      failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view)) →
      Doomed cert (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view)).history) :
    Soundness.uniformProb (Finset.univ.filter fun table : (key : Key) → Answer key =>
      failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view))) ≤
      (n : ℚ)*epsilon := by
  classical
  have bound := memo_transition_bound cert policy epsilon nonnegative hazard n cursor view cache recorded clean
  have coupling := RawOracleCoupling.table_eq_memo (program policy n cursor view) cache
    (fun view => if Dirty cert view.history then (1 : ℚ) else 0)
  have tableBound := coupling.trans_le bound
  have covered : average (fun table : (key : Key) → Answer key =>
      if failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view))
        then (1 : ℚ) else 0) ≤ (n : ℚ)*epsilon := by
    apply le_trans _ tableBound
    apply average_mono
    intro table
    by_cases bad : failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view))
    · have transition := execution_has_transition cert policy n cursor view causal initialCoherent
        (RawOracleCoupling.overlay cache table) (endpoint table bad)
      simp [bad,transition]
    · simp only [bad,↓reduceIte]; split <;> norm_num
  simpa only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using covered

/-- Empty-view PCS game with exactly the requested Q+k dependence. First-capture
metadata invariants are proved internally from the empty cache. The pointwise
endpoint cover, structural causality, and local fiber are the adapter interfaces. -/
theorem accepted_failure_probability [Fintype Key]
    (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard cert epsilon)
    (Q k : Nat) (causal : Causal cert policy (Q+k) 0 initial)
    (failure : View Key Answer Public → Prop)
    (endpoint : ∀ table : (key : Key) → Answer key,
      failure (Sampling.eval table (program policy (Q+k) 0 initial)) →
      Doomed cert (Sampling.eval table (program policy (Q+k) 0 initial)).history) :
    Soundness.uniformProb (Finset.univ.filter fun table : (key : Key) → Answer key =>
      failure (Sampling.eval table (program policy (Q+k) 0 initial))) ≤
      ((Q+k : Nat) : ℚ)*epsilon := by
  exact fixed_prefix_failure_probability cert policy epsilon nonnegative hazard (Q+k) 0 initial
    (fun _ => none) (by intro key answer hit; cases hit) (by simp [initial,Dirty])
    (by simp [initial,Doomed]) causal failure endpoint

end Probability

/-- The final verifier receives the entire adversarial history but gets only k
additional challenge slots, sharing the adversary's global registry and cache. -/
def phases (Q : Nat) (adversary verifier : Policy Key Answer Public) : Policy Key Answer Public where
  choose cursor history := if cursor < Q then adversary.choose cursor history
    else verifier.choose (cursor-Q) history
  prepare cursor history key := if cursor < Q then adversary.prepare cursor history key
    else verifier.prepare (cursor-Q) history key

#print axioms registry_never_overwrites
#print axioms execution_has_transition
#print axioms memo_transition_bound
#print axioms accepted_failure_probability
#print axioms fixed_prefix_failure_probability
end Whir.PCSStateRestoration.Adaptive
