import Whir.AnchoredFiatShamirSecurity

/-! The actual contiguous 32-byte output-block ROM, globally memoized at original
record keys. Roots are prepared before point blocks; complete byte answers,
including the retained suffix, remain available to all adaptive decisions.
Raw-source grouping and chronological eligibility are proved separately. -/
namespace Whir.AnchoredFiatShamirSecurityROM
open Concrete Protocol CausalGame ParameterBounds CommitmentAnchor
open AnchoredFiatShamirSecurity FiatShamirGame TypedOracleCompiler
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Only completed history reaches the policy. All repeats are actual requests
in the reference table, but the operational compiler memoizes them globally. -/
noncomputable def program {p : Profile} {Key : Type} (policy : Policy p Key) :
    (n : Nat) → AnchoredFiatShamirSecurity.Cache p Key →
      Sampling Key (fun _ => Answer p) (AnchoredFiatShamirSecurity.Cache p Key) n
  | 0, history => .ret history
  | n+1, history => .draw (policy.choose history)
      (fun answer => program policy n (advance policy history answer))

private def Seen {p : Profile} {Key : Type} (history : AnchoredFiatShamirSecurity.Cache p Key)
    (cache : TypedFiatShamirGame.Cache Key (fun _ => Answer p)) : Prop :=
  ∀ key answer, cache key = some answer → ∃ e ∈ history, e.key = key

private theorem lookup_miss {p : Profile} {Key : Type}
    (history : AnchoredFiatShamirSecurity.Cache p Key) (key : Key)
    (miss : lookup history key = none) : ¬ ∃ e ∈ history, e.key = key := by
  classical
  induction history with
  | nil => simp
  | cons e rest ih =>
    by_cases same : e.key = key
    · simp [lookup, same] at miss
    · have tail : lookup rest key = none := by simpa [lookup, same] using miss
      simpa [same] using ih tail

private theorem lookup_key {p : Profile} {Key : Type}
    (history : AnchoredFiatShamirSecurity.Cache p Key) (key : Key) (e : Entry p Key)
    (hit : lookup history key = some e) : e.key = key := by
  classical
  induction history with
  | nil => simp [lookup] at hit
  | cons head rest ih =>
    by_cases same : head.key = key
    · have eq : head = e := by simpa [lookup, same] using hit
      exact eq ▸ same
    · exact ih (by simpa [lookup, same] using hit)

private theorem advance_members {p : Profile} {Key : Type} (policy : Policy p Key)
    (history : AnchoredFiatShamirSecurity.Cache p Key) (answer : Answer p) :
    (∀ e ∈ history, e ∈ advance policy history answer) ∧
      ∃ e ∈ advance policy history answer, e.key = policy.choose history := by
  classical
  unfold advance
  dsimp only
  cases hit : lookup history (policy.choose history) with
  | none =>
    constructor
    · intro item member; exact List.mem_cons_of_mem _ member
    · exact ⟨_,List.mem_cons_self,rfl⟩
  | some e =>
    constructor
    · intro item member; exact List.mem_cons_of_mem _ member
    · exact ⟨e,List.mem_cons_self,lookup_key history _ e hit⟩

private theorem advance_clean {p : Profile} {Key : Type} (policy : Policy p Key)
    (history : AnchoredFiatShamirSecurity.Cache p Key) (clean : ¬ Dirty history)
    (answer : Answer p)
    (sep : ¬ Ambiguous p (policy.prepare history (policy.choose history)).lanes
      (policy.prepare history (policy.choose history)).root answer.1) :
    ¬ Dirty (advance policy history answer) := by
  classical
  unfold advance
  dsimp only
  cases hit : lookup history (policy.choose history) with
  | none =>
    simp only [Dirty, List.mem_cons, exists_eq_or_imp]
    exact not_or.mpr ⟨sep,clean⟩
  | some e =>
    have member : e ∈ history := List.mem_of_find?_eq_some hit
    simp only [Dirty, List.mem_cons, exists_eq_or_imp]
    exact not_or.mpr ⟨fun bad => clean ⟨e,member,bad⟩,clean⟩

private theorem memo_bound {p : Profile} {Key : Type} [DecidableEq Key]
    (policy : Policy p Key) (n : Nat) (history : AnchoredFiatShamirSecurity.Cache p Key)
    (cache : TypedFiatShamirGame.Cache Key (fun _ => Answer p))
    (seen : Seen history cache) (clean : ¬ Dirty history) :
    Sampling.expectation (fun result => if Dirty result.1 then (1 : ℚ) else 0)
      (RawOracleCoupling.memo (program policy n history) cache) ≤ (n : ℚ)/2^124 := by
  classical
  induction n generalizing history cache with
  | zero => simp [program, RawOracleCoupling.memo, Sampling.expectation, clean]
  | succ n ih =>
    let key := policy.choose history
    have stepSeen (answer : Answer p) :
        Seen (advance policy history answer) (TypedFiatShamirGame.put cache key answer) := by
      intro wanted value present
      by_cases same : wanted = key
      · subst wanted
        exact (advance_members policy history answer).2
      · have old : cache wanted = some value := by
          simpa only [TypedFiatShamirGame.put_other _ _ _ _ same] using present
        obtain ⟨e,member,equal⟩ := seen wanted value old
        exact ⟨e,(advance_members policy history answer).1 e member,equal⟩
    have oldSeen (answer : Answer p) : Seen (advance policy history answer) cache := by
      intro wanted value present
      obtain ⟨e,member,equal⟩ := seen wanted value present
      exact ⟨e,(advance_members policy history answer).1 e member,equal⟩
    cases hit : cache key with
    | some answer =>
      have actualHit : ∃ e, lookup history key = some e := by
        cases find : lookup history key with
        | some e => exact ⟨e,rfl⟩
        | none => exact False.elim (lookup_miss history key find (seen key answer hit))
      obtain ⟨e,find⟩ := actualHit
      have continuedClean : ¬ Dirty (advance policy history answer) := by
        rw [repeated_key policy history e find answer]
        have member : e ∈ history := List.mem_of_find?_eq_some find
        simp only [Dirty, List.mem_cons, exists_eq_or_imp]
        exact not_or.mpr ⟨fun bad => clean ⟨e,member,bad⟩,clean⟩
      have actualHit : cache (policy.choose history) = some answer := hit
      simp only [program, RawOracleCoupling.memo, actualHit, Sampling.expectation_pad]
      have mono : (n : ℚ)/2^124 ≤ ((n+1 : Nat) : ℚ)/2^124 :=
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (by positivity)
      exact (ih _ _ (oldSeen answer) continuedClean).trans mono
    | none =>
      have actualMiss : cache (policy.choose history) = none := hit
      simp only [program, RawOracleCoupling.memo, actualMiss, Sampling.expectation]
      let bad := fun answer : Answer p =>
        Ambiguous p (policy.prepare history key).lanes (policy.prepare history key).root answer.1
      have fibers (answer : Answer p) :
          Sampling.expectation (fun result => if Dirty result.1 then (1 : ℚ) else 0)
            (RawOracleCoupling.memo (program policy n (advance policy history answer))
              (TypedFiatShamirGame.put cache key answer)) ≤
          (if bad answer then 1 else 0) + (n : ℚ)/2^124 := by
        by_cases badPoint : bad answer
        · have one := Sampling.expectation_le_one
            (fun result : AnchoredFiatShamirSecurity.Cache p Key ×
              TypedFiatShamirGame.Cache Key (fun _ => Answer p) =>
                if Dirty result.1 then (1 : ℚ) else 0)
            (fun result => by split <;> norm_num)
            (RawOracleCoupling.memo (program policy n (advance policy history answer))
              (TypedFiatShamirGame.put cache key answer))
          simpa [badPoint] using one.trans
            (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg n) (by positivity)))
        · simpa [badPoint] using ih _ _ (stepSeen answer)
            (advance_clean policy history clean answer badPoint)
      have badBound : average (fun answer : Answer p => if bad answer then (1 : ℚ) else 0) ≤
          (1 : ℚ)/2^124 := by
        change average (fun answer : Point p × Tail p =>
          if Ambiguous p (policy.prepare history key).lanes
            (policy.prepare history key).root answer.1 then (1 : ℚ) else 0) ≤ _
        rw [WHIRObservableSecurity.average_product (X := Point p) (Y := Tail p)]
        change average (fun point : Point p => average (fun _ : Tail p =>
          if Ambiguous p (policy.prepare history key).lanes
            (policy.prepare history key).root point then (1 : ℚ) else 0)) ≤ _
        simp_rw [average_const]
        have separation := ambiguity_probability_numeric p
          (policy.prepare history key).lanes (policy.prepare history key).root
          (policy.prepare history key).occupied.2
        simpa only [average, Soundness.uniformProb, Finset.card_filter,
          Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using separation
      have bound : average (fun answer : Answer p =>
          Sampling.expectation (fun result => if Dirty result.1 then (1 : ℚ) else 0)
            (RawOracleCoupling.memo (program policy n (advance policy history answer))
              (TypedFiatShamirGame.put cache key answer))) ≤
          (1 : ℚ)/2^124 + (n : ℚ)/2^124 := (average_mono fibers).trans (by
        rw [average_add, average_const]
        exact add_le_add badBound le_rfl)
      calc
        _ ≤ (1 : ℚ)/2^124 + (n : ℚ)/2^124 := bound
        _ = _ := by push_cast; ring

/-- Actual uniform finite vector ROM, including repeated keys, with adaptive
roots prepared before their first answer. Internal cache invariants are PROVED
from the empty cache, not handed to the adversary as endpoint assumptions. -/
theorem table_ambiguity_probability {p : Profile} {Key : Type} [Fintype Key]
    [DecidableEq Key] (policy : Policy p Key) (n : Nat) :
    Soundness.uniformProb (Finset.univ.filter fun table : Key → Answer p =>
      Dirty (Sampling.eval table (program policy n []))) ≤ (n : ℚ)/2^124 := by
  classical
  have coupled := RawOracleCoupling.empty_table_eq_memo (program policy n [])
    (fun history => if Dirty history then (1 : ℚ) else 0)
  have bounded := memo_bound policy n [] (fun _ => none)
    (by intro key answer present; contradiction) (by simp [Dirty])
  rw [← coupled] at bounded
  simpa only [average, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using bounded

/-- Each original record has ceil(24*logN/32) distinct output-block fibers.
The joint codec retains every byte of every raw reply. -/
def blockTableCodec (p : Profile) (Key : Type) :
    ((Key × Fin (AnchoredFiatShamirSecurityCodec.blockCount (config p).logN)) → Digest32) ≃
      (Key → Answer p) :=
  (Equiv.curry Key (Fin (AnchoredFiatShamirSecurityCodec.blockCount (config p).logN))
    Digest32).trans
    (Equiv.piCongrRight fun _ => AnchoredFiatShamirSecurityCodec.vectorParts (config p).logN)

theorem block_table_ambiguity_probability {p : Profile} {Key : Type} [Fintype Key]
    [DecidableEq Key] (policy : Policy p Key) (n : Nat) :
    Soundness.uniformProb (Finset.univ.filter fun table :
      (Key × Fin (AnchoredFiatShamirSecurityCodec.blockCount (config p).logN)) → Digest32 =>
      Dirty (Sampling.eval (blockTableCodec p Key table) (program policy n []))) ≤
      (n : ℚ)/2^124 := by
  classical
  have transport := RawOracleCoupling.average_equiv (blockTableCodec p Key)
    (fun table => if Dirty (Sampling.eval table (program policy n [])) then (1 : ℚ) else 0)
  have probabilityEq :
      Soundness.uniformProb (Finset.univ.filter fun table :
        (Key × Fin (AnchoredFiatShamirSecurityCodec.blockCount (config p).logN)) → Digest32 =>
        Dirty (Sampling.eval (blockTableCodec p Key table) (program policy n []))) =
      Soundness.uniformProb (Finset.univ.filter fun table : Key → Answer p =>
        Dirty (Sampling.eval table (program policy n []))) := by
    simpa only [average, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using transport
  rw [probabilityEq]
  exact table_ambiguity_probability policy n

abbrev BlockOracle (p : Profile) (Key : Type) :=
  (Key × Fin (AnchoredFiatShamirSecurityCodec.blockCount (config p).logN)) → Digest32

noncomputable def historyOf {p : Profile} {Key : Type} (policy : Policy p Key)
    (n : Nat) (table : BlockOracle p Key) :=
  Sampling.eval (blockTableCodec p Key table) (program policy n [])

/-- Final selection is from an actually answered root/shape/point record, not a
root chosen using an unqueried table point. The advertised value is still free. -/
abbrev TableSelector {p : Profile} {Key : Type} (policy : Policy p Key) (n : Nat) :=
  (table : BlockOracle p Key) → Option {e : Entry p Key // e ∈ historyOf policy n table}

noncomputable def TableFailure {p : Profile} {Key : Type} (policy : Policy p Key)
    (n : Nat) (select : TableSelector policy n) (advertised : BlockOracle p Key → E)
    (opening : BlockOracle p Key → Array Claim) (strategy : BlockOracle p Key → Strategy)
    (sample : BlockOracle p Key × Tape (config p)) : Prop :=
  match select sample.1 with
  | none => False
  | some e => openingFailure p (chosenCommitment e.val (advertised sample.1))
      (opening sample.1) (strategy sample.1) sample.2

/-- Adaptive byte-stream ROM anchor selection followed by one independent causal
opening tape. Final selection may inspect the entire public raw block table;
pre-point root preparation still sees completed history only. This theorem
does not identify that independent opening tape with the native verifier body. -/
theorem block_table_unique_opening_probability {p : Profile} {Key : Type}
    [Fintype Key] [DecidableEq Key] (policy : Policy p Key) (n : Nat)
    (select : TableSelector policy n) (advertised : BlockOracle p Key → E)
    (opening : BlockOracle p Key → Array Claim) (strategy : BlockOracle p Key → Strategy)
    (opening_cap : ∀ table, (opening table).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      (TableFailure policy n select advertised opening strategy)) ≤
      (n : ℚ)/2^124 + (1 : ℚ)/2^73 := by
  classical
  apply RingMapBatching.conditional_error
    (fun table : BlockOracle p Key => Dirty (historyOf policy n table))
    _ _ _ (by positivity) (block_table_ambiguity_probability policy n)
  intro table clean
  cases chosen : select table with
  | none => simp [TableFailure, chosen, Soundness.uniformProb]
  | some e =>
    have sep : ¬ Ambiguous p e.val.commitment.lanes e.val.commitment.root
        e.val.commitment.point := fun bad => clean ⟨e.val,e.property,bad⟩
    simpa only [TableFailure, chosen] using
      (unique_opening_probability p (chosenCommitment e.val (advertised table))
        sep (opening table) (strategy table)).trans
        (production_interactive p _ (opening_cap table))

private theorem profile_blocks : ∀ p : Profile,
    1 ≤ AnchoredFiatShamirSecurityCodec.blockCount (config p).logN := by
  decide +kernel

/-- Source resource accounting charges actual 32-byte output blocks, not one
digest per scalar. Repeated requests are conservatively charged too. -/
theorem block_table_unique_opening_numeric {p : Profile} {Key : Type}
    [Fintype Key] [DecidableEq Key] (policy : Policy p Key) (n Q : Nat)
    (blockBudget : n * AnchoredFiatShamirSecurityCodec.blockCount (config p).logN ≤ Q)
    (compression : Q ≤ 2^60)
    (select : TableSelector policy n) (advertised : BlockOracle p Key → E)
    (opening : BlockOracle p Key → Array Claim) (strategy : BlockOracle p Key → Strategy)
    (opening_cap : ∀ table, (opening table).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      (TableFailure policy n select advertised opening strategy)) ≤
      (1 : ℚ)/2^64 + (1 : ℚ)/2^73 := by
  have attempts : n ≤ 2^60 := calc
    n = n*1 := by simp
    _ ≤ n*AnchoredFiatShamirSecurityCodec.blockCount (config p).logN :=
      Nat.mul_le_mul_left n (profile_blocks p)
    _ ≤ Q := blockBudget
    _ ≤ 2^60 := compression
  apply (block_table_unique_opening_probability policy n select advertised opening strategy
    opening_cap).trans
  apply add_le_add _ le_rfl
  have h : (n : ℚ) ≤ 2^60 := by exact_mod_cast attempts
  exact (div_le_div_of_nonneg_right h (by positivity)).trans (by norm_num)


end Whir.AnchoredFiatShamirSecurityROM

#print axioms Whir.AnchoredFiatShamirSecurityROM.table_ambiguity_probability
#print axioms Whir.AnchoredFiatShamirSecurityROM.block_table_ambiguity_probability
#print axioms Whir.AnchoredFiatShamirSecurityROM.block_table_unique_opening_probability
#print axioms Whir.AnchoredFiatShamirSecurityROM.block_table_unique_opening_numeric
