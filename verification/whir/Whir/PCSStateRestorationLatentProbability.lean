import Whir.PCSStateRestoration

/-! Finite first-disclosure union bound with events depending on latent table
coordinates. No ancestor is warmed and no adversarial query is restricted. -/
namespace Whir.PCSStateRestoration.Latent
open TypedOracleCompiler TypedFiatShamirGame
open FiatShamirGame (average average_mono average_const average_add)

set_option autoImplicit false

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {R : Type w}

abbrev Table (Key : Type u) (Answer : Key → Type v) := (key : Key) → Answer key
abbrev Erased (Answer : Key → Type v) (key : Key) := (other : {other : Key // other ≠ key}) → Answer other.val

def erase (key : Key) (table : Table Key Answer) : Erased Answer key := fun other => table other.val

section Execution
variable [DecidableEq Key]

@[simp] theorem erase_update (key : Key) (table : Table Key Answer) (answer : Answer key) :
    erase key (Function.update table key answer) = erase key table := by
  funext other
  simp [erase,Function.update_of_ne other.property]

/-- The actual complete public view before the first request of a selected key.
`none` means that the computation never requests that key. -/
def firstDisclosure (target : Key) : {n : Nat} → Sampling Key Answer R n → Table Key Answer →
    Option (List (Sigma Answer))
  | _, .ret _, _ => none
  | _, .draw key next, table =>
    if key = target then some [] else
      (firstDisclosure target (next (table key)) table).map (fun past => ⟨key,table key⟩ :: past)

/-- First-query selection and its entire preceding view are independent of
that key's answer. This is proved from the actual adaptive Sampling execution,
not a freshness premise on the adversary or an observer restriction. -/
theorem first_disclosure_answer_independent {n : Nat} (target : Key)
    (source : Sampling Key Answer R n) (table : Table Key Answer) (answer : Answer target) :
    firstDisclosure target source (Function.update table target answer) = firstDisclosure target source table := by
  induction source with
  | ret result => rfl
  | draw key next ih =>
    by_cases same : key = target
    · simp [firstDisclosure,same]
    · simp only [firstDisclosure,same,↓reduceIte,Function.update_of_ne same,ih]

/-- The selected first-disclosure prefix really precedes a request in the
ordinary operational trace. Subsequent requests remain in that trace. -/
theorem first_disclosure_execution {n : Nat} (target : Key) (source : Sampling Key Answer R n)
    (table : Table Key Answer) (past : List (Sigma Answer))
    (selected : firstDisclosure target source table = some past) :
    ∃ suffix, (Sampling.execute table source).2 = past ++ (⟨target,table target⟩ :: suffix) ∧
      ∀ entry ∈ past, entry.1 ≠ target := by
  induction source generalizing past with
  | ret result => simp [firstDisclosure] at selected
  | draw key next ih =>
    by_cases same : key = target
    · subst key
      simp only [firstDisclosure,↓reduceIte,Option.some.injEq] at selected
      subst past
      exact ⟨(Sampling.execute table (next (table target))).2,rfl,by simp⟩
    · simp only [firstDisclosure,same,↓reduceIte] at selected
      cases found : firstDisclosure target (next (table key)) table with
      | none => simp [found] at selected
      | some before =>
        simp only [found,Option.map_some,Option.some.injEq] at selected
        subst past
        obtain ⟨suffix,trace,absent⟩ := ih (table key) before found
        refine ⟨suffix,?_,?_⟩
        · simp only [Sampling.execute,List.cons_append,trace]
        · intro entry member
          rcases List.mem_cons.mp member with equal | member
          · subst entry; exact same
          · exact absent entry member

/-- Conversely every operational request is selected by the first-disclosure
finder. Together with `first_disclosure_execution`, this rules out a merely
plausible recognizer that ignores some actually requested keys. -/
theorem first_disclosure_complete {n : Nat} (target : Key) (source : Sampling Key Answer R n)
    (table : Table Key Answer)
    (observed : ∃ entry ∈ (Sampling.execute table source).2, entry.1 = target) :
    ∃ past, firstDisclosure target source table = some past := by
  induction source with
  | ret result => simp [Sampling.execute] at observed
  | draw key next ih =>
    by_cases same : key = target
    · exact ⟨[],by simp [firstDisclosure,same]⟩
    · obtain ⟨entry,member,equal⟩ := observed
      rcases List.mem_cons.mp member with first | member
      · subst entry; exact False.elim (same equal)
      · obtain ⟨past,selected⟩ := ih (table key) ⟨entry,member,equal⟩
        exact ⟨⟨key,table key⟩ :: past,by simp [firstDisclosure,same,selected]⟩

/-- Whether the actual computation ever requests a key is answer-independent,
not just the syntactic recognizer's result. Repeated and later requests remain
unrestricted after that first exposure. -/
theorem queried_key_answer_independent {n : Nat} (target : Key)
    (source : Sampling Key Answer R n) (table : Table Key Answer) (answer : Answer target) :
    (∃ entry ∈ (Sampling.execute (Function.update table target answer) source).2, entry.1 = target) ↔
      ∃ entry ∈ (Sampling.execute table source).2, entry.1 = target := by
  have transfer (old new : Table Key Answer)
      (same : firstDisclosure target source old = firstDisclosure target source new)
      (observed : ∃ entry ∈ (Sampling.execute old source).2, entry.1 = target) :
      ∃ entry ∈ (Sampling.execute new source).2, entry.1 = target := by
    obtain ⟨past,selected⟩ := first_disclosure_complete target source old observed
    obtain ⟨suffix,trace,_⟩ := first_disclosure_execution target source new past (same ▸ selected)
    exact ⟨⟨target,new target⟩,by rw [trace]; simp,rfl⟩
  have same := first_disclosure_answer_independent target source table answer
  exact ⟨transfer _ _ same,transfer _ _ same.symm⟩

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- One charge per distinct first exposure. Events may depend on all other
latent coordinates of the same table, including ancestors queried later. -/
noncomputable def count (bad : Key → Table Key Answer → Prop) : {n : Nat} →
    Sampling Key Answer R n → Cache Key Answer → Table Key Answer → Nat
  | _, .ret _, _, _ => 0
  | _, .draw key next, cache, table =>
    match cache key with
    | some _ => count bad (next (table key)) cache table
    | none => (if bad key table then 1 else 0) +
        count bad (next (table key)) (put cache key (table key)) table

def ObservedBad (bad : Key → Table Key Answer → Prop) {n : Nat}
    (source : Sampling Key Answer R n) (table : Table Key Answer) : Prop :=
  ∃ entry ∈ (Sampling.execute table source).2, bad entry.1 table

/-- Pointwise coverage by a first exposure, including arbitrary repeats. -/
theorem observed_bad_count_positive (bad : Key → Table Key Answer → Prop) {n : Nat}
    (source : Sampling Key Answer R n) (cache : Cache Key Answer) (table : Table Key Answer)
    (safe : ∀ key answer, cache key = some answer → ¬ bad key table)
    (observed : ObservedBad bad source table) : 0 < count bad source cache table := by
  induction source generalizing cache with
  | ret result => simp [ObservedBad,Sampling.execute] at observed
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      obtain ⟨entry,member,event⟩ := observed
      rcases List.mem_cons.mp member with equal | member
      · subst entry; exact False.elim (safe key answer hit event)
      · simp only [count,hit]
        exact ih (table key) cache safe ⟨entry,member,event⟩
    | none =>
      by_cases badNow : bad key table
      · simp only [count,hit,badNow,↓reduceIte]
        omega
      · obtain ⟨entry,member,event⟩ := observed
        rcases List.mem_cons.mp member with equal | member
        · subst entry; exact False.elim (badNow event)
        · have nextSafe : ∀ wanted value, put cache key (table key) wanted = some value → ¬ bad wanted table := by
            intro wanted value present
            by_cases same : wanted = key
            · subst wanted; exact badNow
            · exact safe wanted value (by simpa [put_other,same] using present)
          simpa only [count,hit,badNow,↓reduceIte,zero_add] using
            ih (table key) (put cache key (table key)) nextSafe ⟨entry,member,event⟩

end Execution

section Probability
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable [DecidableEq Key] [Fintype Key]
variable [∀ key, Fintype (Answer key)] [∀ key, Nonempty (Answer key)]

/-- Uniform fiber condition with the complete remaining table fixed. Later
coins are not averaged away or replaced by independent placeholder events. -/
def FiberBound (bad : Key → Table Key Answer → Prop) (epsilon : ℚ) : Prop :=
  ∀ key table, average (fun answer : Answer key =>
    if bad key (Function.update table key answer) then (1 : ℚ) else 0) ≤ epsilon

/-- Exact adaptive finite-table first-disclosure bound. The induction uses the
causal Sampling continuations and exact selected-coordinate disintegration;
the latent event itself need not be measurable from the disclosed history. -/
theorem adaptive_first_disclosure_bound (bad : Key → Table Key Answer → Prop)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (fiber : FiberBound bad epsilon)
    {n : Nat} (source : Sampling Key Answer R n) (cache : Cache Key Answer) :
    average (fun table : Table Key Answer =>
      (count bad source cache (RawOracleCoupling.overlay cache table) : ℚ)) ≤ (n : ℚ)*epsilon := by
  induction source generalizing cache with
  | ret result =>
    simp only [count,Nat.cast_zero,average_const]
    exact mul_nonneg (Nat.cast_nonneg _) nonnegative
  | @draw n key next ih =>
    cases hit : cache key with
    | some answer =>
      have answered (table : Table Key Answer) : RawOracleCoupling.overlay cache table key = answer := by
        simp [RawOracleCoupling.overlay,hit]
      simp only [count,hit]
      simp_rw [answered]
      exact (ih answer cache).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) nonnegative)
    | none =>
      rw [RawOracleCoupling.overlay_average cache key hit
        (fun table => (count bad (.draw key next) cache table : ℚ))]
      have answered (answer : Answer key) (table : Table Key Answer) :
          RawOracleCoupling.overlay (put cache key answer) table key = answer := by
        simp [RawOracleCoupling.overlay]
      simp only [count,hit,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      simp_rw [answered,average_add]
      have localBound : average (fun answer : Answer key => average (fun table : Table Key Answer =>
          if bad key (RawOracleCoupling.overlay (put cache key answer) table) then (1 : ℚ) else 0)) ≤ epsilon := by
        rw [RawOracleCoupling.average_comm]
        have perRest (table : Table Key Answer) : average (fun answer : Answer key =>
            if bad key (RawOracleCoupling.overlay (put cache key answer) table) then (1 : ℚ) else 0) ≤ epsilon := by
          simpa only [RawOracleCoupling.overlay_put] using fiber key (RawOracleCoupling.overlay cache table)
        exact (average_mono perRest).trans (le_of_eq (average_const epsilon))
      have continued : average (fun answer : Answer key => average (fun table : Table Key Answer =>
          (count bad (next answer) (put cache key answer)
            (RawOracleCoupling.overlay (put cache key answer) table) : ℚ))) ≤ (n : ℚ)*epsilon := by
        exact (average_mono (fun answer => ih answer (put cache key answer))).trans (le_of_eq (average_const _))
      calc
        _ ≤ epsilon + (n : ℚ)*epsilon := add_le_add localBound continued
        _ = ((n : ℚ)+1)*epsilon := by ring

/-- Generic failure coverage; the endpoint is pointwise, not a probability or
soundness assumption. The bound charges requests rather than the key universe. -/
theorem covered_failure_probability (bad : Key → Table Key Answer → Prop)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (fiber : FiberBound bad epsilon)
    {n : Nat} (source : Sampling Key Answer R n) (failure : Table Key Answer → Prop)
    (cover : ∀ table, failure table → ObservedBad bad source table) :
    Soundness.uniformProb (Finset.univ.filter failure) ≤ (n : ℚ)*epsilon := by
  classical
  have bounded := adaptive_first_disclosure_bound bad epsilon nonnegative fiber source (fun _ => none)
  simp only [RawOracleCoupling.overlay_empty] at bounded
  have covered : average (fun table : Table Key Answer => if failure table then (1 : ℚ) else 0) ≤
      (n : ℚ)*epsilon := by
    apply le_trans _ bounded
    apply average_mono
    intro table
    by_cases failed : failure table
    · have positive := observed_bad_count_positive bad source (fun _ => none) table
        (by intro key answer hit; cases hit) (cover table failed)
      simp only [failed,↓reduceIte]
      exact_mod_cast positive
    · simp only [failed,↓reduceIte]
      positivity
  simpa only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using covered

end Probability

#print axioms first_disclosure_answer_independent
#print axioms first_disclosure_execution
#print axioms first_disclosure_complete
#print axioms queried_key_answer_independent
#print axioms adaptive_first_disclosure_bound
#print axioms covered_failure_probability
end Whir.PCSStateRestoration.Latent
