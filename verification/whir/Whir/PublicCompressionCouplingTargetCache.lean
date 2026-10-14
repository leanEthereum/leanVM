import Whir.PublicCompressionCouplingHidden

/-! Operational consequences of the actual fresh-target alarm. A quiet private
run creates no new target-valued cache entries. These are cache/trace lemmas,
not a supplied stochastic certificate: the alarm probability is already derived
from the actual uniform finite experiment in PublicCompressionCouplingHidden. -/
namespace Whir.PublicCompressionCouplingTargetCache
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open TypedFiatShamirGame RawOracleCoupling

variable {K R : Type} [DecidableEq K]
abbrev Computation (K R : Type) (n : Nat) := Sampling K (fun _ => Digest32) R n

/-- Memo execution never removes or changes an already populated coordinate. -/
theorem memo_extends (table : K → Digest32) {n : Nat} (p : Computation K R n)
    (cache : K → Option Digest32) {key : K} {answer : Digest32}
    (stored : cache key = some answer) :
    (Sampling.eval table (memo p cache)).2 key = some answer := by
  induction p generalizing cache with
  | ret r => exact stored
  | draw input next ih =>
    cases hit : cache input with
    | some value =>
      simp only [memo,hit,Sampling.eval_pad]
      exact ih value cache stored
    | none =>
      simp only [memo,hit,Sampling.eval]
      apply ih (table input)
      by_cases same : key=input
      · subst key
        simp only [hit] at stored
        cases stored
      · simpa only [put_other _ _ _ _ same] using stored

/-- Stronger than the requested consistent-cache version: no consistency
premise is needed, since the alarm and memo follow identical cached answers. -/
theorem target_support (table : K → Digest32) (targets : Finset Digest32) {n : Nat}
    (p : Computation K R n) (cache : K → Option Digest32)
    (quiet : PublicCompressionCouplingTargets.alarm table targets p cache = false)
    {key : K} {answer : Digest32}
    (stored : (Sampling.eval table (memo p cache)).2 key = some answer)
    (target : answer ∈ targets) : cache key = some answer := by
  induction p generalizing cache with
  | ret r => exact stored
  | draw input next ih =>
    cases hit : cache input with
    | some value =>
      simp only [memo,hit,Sampling.eval_pad] at stored
      simp only [PublicCompressionCouplingTargets.alarm,hit] at quiet
      exact ih value cache quiet stored
    | none =>
      simp only [PublicCompressionCouplingTargets.alarm,hit] at quiet
      have parts := Bool.or_eq_false_iff.mp quiet
      have fresh := of_decide_eq_false parts.1
      simp only [memo,hit,Sampling.eval] at stored
      have old := ih (table input) (put cache input (table input)) parts.2 stored
      by_cases same : key=input
      · subst key
        simp only [put_self,Option.some.injEq] at old
        exact False.elim (fresh (old.symm ▸ target))
      · simpa only [put_other _ _ _ _ same] using old

 theorem put_consistent (table : K → Digest32) (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer) (input : K) :
    ∀ key answer, (put cache input (table input)) key=some answer → table key=answer := by
  intro key answer stored
  by_cases same : key=input
  · subst key
    simpa only [put_self,Option.some.injEq] using stored
  · exact consistent key answer (by simpa only [put_other _ _ _ _ same] using stored)

/-- All actual original-table trace entries are recorded by the completed memo
cache. Consistency is an interpreter invariant, proved for public execution
from its empty initial cache, not a soundness premise. -/
theorem trace_recorded (table : K → Digest32) {n : Nat} (p : Computation K R n)
    (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer)
    {key : K} {answer : Digest32}
    (member : (⟨key,answer⟩ : Sigma (fun _ : K => Digest32)) ∈ (Sampling.execute table p).2) :
    (Sampling.eval table (memo p cache)).2 key=some answer := by
  induction p generalizing cache with
  | ret r => simp [Sampling.execute] at member
  | draw input next ih =>
    simp only [Sampling.execute,List.mem_cons] at member
    cases hit : cache input with
    | some value =>
      simp only [memo,hit,Sampling.eval_pad]
      have actual := consistent input value hit
      rcases member with equal | later
      · have sameKey : key=input := congrArg Sigma.fst equal
        have sameAnswer : answer=table input :=
          congrArg (fun entry : Sigma (fun _ : K => Digest32) => entry.2) equal
        subst key
        subst answer
        apply memo_extends
        simpa only [actual] using hit
      · rw [← actual]
        exact ih (table input) cache consistent later
    | none =>
      simp only [memo,hit,Sampling.eval]
      rcases member with equal | later
      · have sameKey : key=input := congrArg Sigma.fst equal
        have sameAnswer : answer=table input :=
          congrArg (fun entry : Sigma (fun _ : K => Digest32) => entry.2) equal
        subst key
        subst answer
        apply memo_extends
        exact put_self _ _ _
      · exact ih (table input) (put cache input (table input))
          (put_consistent table cache consistent input) later

/-- Converse to trace_recorded: completed memo entries were either present
initially or were returned by an actual original-table execution query. -/
theorem memo_trace_origin (table : K → Digest32) {n : Nat} (p : Computation K R n)
    (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer)
    {key : K} {answer : Digest32}
    (stored : (Sampling.eval table (memo p cache)).2 key=some answer) :
    cache key=some answer ∨
      (⟨key,answer⟩ : Sigma (fun _ : K => Digest32)) ∈ (Sampling.execute table p).2 := by
  induction p generalizing cache with
  | ret r => exact Or.inl stored
  | draw input next ih =>
    cases hit : cache input with
    | some value =>
      simp only [memo,hit,Sampling.eval_pad] at stored
      have actual := consistent input value hit
      rcases ih value cache consistent stored with old | queried
      · exact Or.inl old
      · apply Or.inr
        simp only [Sampling.execute]
        apply List.mem_cons_of_mem
        simpa only [actual] using queried
    | none =>
      simp only [memo,hit,Sampling.eval] at stored
      rcases ih (table input) (put cache input (table input))
        (put_consistent table cache consistent input) stored with old | queried
      · by_cases same : key=input
        · subst key
          simp only [put_self,Option.some.injEq] at old
          subst answer
          exact Or.inr (by simp [Sampling.execute])
        · exact Or.inl (by simpa only [put_other _ _ _ _ same] using old)
      · exact Or.inr (by simpa only [Sampling.execute] using List.mem_cons_of_mem _ queried)

theorem memo_empty_trace (table : K → Digest32) {n : Nat} (p : Computation K R n)
    {key : K} {answer : Digest32}
    (stored : (Sampling.eval table (memo p (fun _ => none))).2 key=some answer) :
    (⟨key,answer⟩ : Sigma (fun _ : K => Digest32)) ∈ (Sampling.execute table p).2 := by
  rcases memo_trace_origin table p (fun _ => none)
    (by intro key value impossible; cases impossible) stored with impossible | queried
  · cases impossible
  · exact queried

#print axioms memo_trace_origin
#print axioms memo_empty_trace

 theorem trace_target_initial (table : K → Digest32) (targets : Finset Digest32)
    {n : Nat} (p : Computation K R n) (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer)
    (quiet : PublicCompressionCouplingTargets.alarm table targets p cache=false)
    {key : K} {answer : Digest32}
    (member : (⟨key,answer⟩ : Sigma (fun _ : K => Digest32)) ∈ (Sampling.execute table p).2)
    (target : answer ∈ targets) : cache key=some answer :=
  target_support table targets p cache quiet (trace_recorded table p cache consistent member) target

open Classical in
/-- Any target-valued actual private seed inspection draw was already sampled
in the public pinned-simulator phase. The public cache consistency is derived
here from actual empty-cache memo execution. -/
theorem inspected_seed_target_public {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p)
    (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (quiet : PublicCompressionCouplingMixed.hiddenGuess Q iv p counted table=false)
    {input : Node} {answer : Digest32}
    (member : (⟨Sum.inl input,answer⟩ : Sigma (fun _ : PublicCompressionCouplingMixed.Key Q => Digest32)) ∈
      (Sampling.execute table (PublicCompressionCouplingMixed.privateInspection Q iv
        (Sampling.eval table (memo (PublicCompressionCouplingMixed.certifiedPublic Q iv p counted)
          (fun _ => none))).1)).2)
    (target : answer ∈ PublicCompressionCouplingMixed.publicCVTargets
      (Sampling.eval table (memo (PublicCompressionCouplingMixed.certifiedPublic Q iv p counted)
        (fun _ => none))).1.val.observations) :
    (Sampling.eval table (memo (PublicCompressionCouplingMixed.certifiedPublic Q iv p counted)
      (fun _ => none))).2 (.inl input)=some answer := by
  apply trace_target_initial table _ _ _ _ quiet member target
  exact memo_eval_consistent _ _ table (by intro key value impossible; cases impossible)

#print axioms target_support
#print axioms trace_recorded
#print axioms inspected_seed_target_public
end Whir.PublicCompressionCouplingTargetCache
