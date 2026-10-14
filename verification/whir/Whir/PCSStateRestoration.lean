import Whir.RawOracleCoupling

/-! Reusable finite memo-interpreter facts for PCS state restoration.
The adaptive first-registration game is in PCSStateRestorationAdaptive. -/
namespace Whir.PCSStateRestoration
open TypedOracleCompiler TypedFiatShamirGame
open FiatShamirGame (average)

set_option autoImplicit false

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {R : Type w} [DecidableEq Key]

/-- Padding a request cap does not create an additional fresh draw, even after
memoization. This is an exact expectation identity for every payoff. -/
theorem memo_expectation_pad [∀ key, Fintype (Answer key)] [∀ key, Nonempty (Answer key)]
    {n m : Nat} (h : n ≤ m) (source : Sampling Key Answer R n)
    (cache : Cache Key Answer) (payoff : R × Cache Key Answer → ℚ) :
    Sampling.expectation payoff (RawOracleCoupling.memo (Sampling.pad h source) cache) =
      Sampling.expectation payoff (RawOracleCoupling.memo source cache) := by
  induction source generalizing m cache with
  | ret r => simp only [Sampling.pad,RawOracleCoupling.memo,Sampling.expectation]
  | draw key next ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases hit : cache key with
      | some answer =>
        simp only [Sampling.pad,RawOracleCoupling.memo,hit,Sampling.expectation_pad]
        exact ih answer _ cache
      | none =>
        simp only [Sampling.pad,RawOracleCoupling.memo,hit,Sampling.expectation]
        apply congrArg average
        funext answer
        exact ih answer _ (put cache key answer)

/-- Every allocated key is distinct and absent from the initial cache. Existing
fixed-prefix answers and repeated requests are not fresh exposures. -/
theorem memo_runs_distinct {n : Nat} (source : Sampling Key Answer R n)
    (cache : Cache Key Answer) (trace : List (Sigma Answer)) (result : R × Cache Key Answer)
    (run : Sampling.Runs (RawOracleCoupling.memo source cache) trace result) :
    (∀ entry ∈ trace, cache entry.1 = none) ∧ (trace.map Sigma.fst).Nodup := by
  induction source generalizing cache trace result with
  | ret value =>
    cases run
    exact ⟨by simp, by simp⟩
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [RawOracleCoupling.memo,hit,Sampling.runs_pad] at run
      exact ih answer cache trace result run
    | none =>
      simp only [RawOracleCoupling.memo,hit] at run
      cases run with
      | @draw _ _ _ tail _ answer rest =>
        obtain ⟨fresh,distinct⟩ := ih answer (put cache key answer) _ _ rest
        have different : ∀ (entry : Sigma Answer), entry ∈ tail → entry.1 ≠ key := by
          intro entry member same
          have absent := fresh entry member
          rw [same,put_self] at absent
          contradiction
        constructor
        · intro entry member
          rcases List.mem_cons.mp member with equal | member
          · subst entry; exact hit
          · simpa only [put_other _ _ _ _ (different entry member)] using fresh entry member
        · rw [List.map_cons,List.nodup_cons]
          refine ⟨?_,distinct⟩
          intro member
          obtain ⟨entry,entryMember,equal⟩ := List.mem_map.mp member
          exact different entry entryMember equal

#print axioms memo_expectation_pad
#print axioms memo_runs_distinct
end Whir.PCSStateRestoration
