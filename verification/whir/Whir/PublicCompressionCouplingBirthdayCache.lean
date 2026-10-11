import Whir.PublicCompressionCouplingBirthday

/-! Actual memo-cache answer injectivity on the complement of the already
proved mixed-table birthday alarm. Coverage and injectivity are operational
cache invariants, discharged from the literal empty cache at the endpoint. -/
namespace Whir.PublicCompressionCouplingBirthdayCache
open FiatShamirGame TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling

variable {K R : Type} [DecidableEq K]
abbrev Computation (K R : Type) (n : Nat) := Sampling K (fun _ => Digest32) R n

def AnswerInjective (cache : K → Option Digest32) : Prop :=
  ∀ a b d, cache a=some d → cache b=some d → a=b

def Covered (cache : K → Option Digest32) (seen : Finset Digest32) : Prop :=
  ∀ key answer, cache key=some answer → answer ∈ seen

 theorem put_covered (cache : K → Option Digest32) (seen : Finset Digest32)
    (covered : Covered cache seen) (input : K) (value : Digest32) :
    Covered (put cache input value) (insert value seen) := by
  intro key answer stored
  by_cases same : key=input
  · subst key
    simp only [put_self,Option.some.injEq] at stored
    subst answer
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (covered key answer
      (by simpa only [put_other _ _ _ _ same] using stored))

 theorem put_injective (cache : K → Option Digest32) (seen : Finset Digest32)
    (covered : Covered cache seen) (injective : AnswerInjective cache)
    (input : K) (value : Digest32) (fresh : value ∉ seen) :
    AnswerInjective (put cache input value) := by
  intro a b d left right
  by_cases sameA : a=input
  · subst a
    have actual : value=d := by simpa only [put_self,Option.some.injEq] using left
    by_cases sameB : b=input
    · exact sameB.symm
    · have old : cache b=some d := by simpa only [put_other _ _ _ _ sameB] using right
      exact False.elim (fresh (actual.symm ▸ covered b d old))
  · by_cases sameB : b=input
    · subst b
      have actual : value=d := by simpa only [put_self,Option.some.injEq] using right
      have old : cache a=some d := by simpa only [put_other _ _ _ _ sameA] using left
      exact False.elim (fresh (actual.symm ▸ covered a d old))
    · exact injective a b d
        (by simpa only [put_other _ _ _ _ sameA] using left)
        (by simpa only [put_other _ _ _ _ sameB] using right)

/-- No cryptographic initial-injectivity premise is used at the empty-cache
specialization below. Both invariants are transported by actual memo steps. -/
theorem alarm_false_cache_injective (table : K → Digest32) {n : Nat}
    (p : Computation K R n) (cache : K → Option Digest32) (seen : Finset Digest32)
    (covered : Covered cache seen) (injective : AnswerInjective cache)
    (quiet : PublicCompressionCouplingBirthday.alarm table p cache seen=false) :
    AnswerInjective (Sampling.eval table (memo p cache)).2 := by
  induction p generalizing cache seen with
  | ret r => exact injective
  | draw input next ih =>
    cases hit : cache input with
    | some value =>
      simp only [memo,hit,Sampling.eval_pad]
      simp only [PublicCompressionCouplingBirthday.alarm,hit] at quiet
      exact ih value cache seen covered injective quiet
    | none =>
      simp only [memo,hit,Sampling.eval]
      simp only [PublicCompressionCouplingBirthday.alarm,hit] at quiet
      have parts := Bool.or_eq_false_iff.mp quiet
      have fresh := of_decide_eq_false parts.1
      exact ih (table input) (put cache input (table input)) (insert (table input) seen)
        (put_covered cache seen covered input (table input))
        (put_injective cache seen covered injective input (table input) fresh) parts.2

 theorem birthday_cache_injective (table : K → Digest32) {n : Nat}
    (p : Computation K R n)
    (quiet : PublicCompressionCouplingBirthday.alarm table p (fun _ => none) ∅=false) :
    ∀ a b d, (Sampling.eval table (memo p (fun _ => none))).2 a=some d →
      (Sampling.eval table (memo p (fun _ => none))).2 b=some d → a=b := by
  apply alarm_false_cache_injective table p (fun _ => none) ∅ _ _ quiet
  · intro key answer impossible
    cases impossible
  · intro a b d impossible
    cases impossible

#print axioms alarm_false_cache_injective
#print axioms birthday_cache_injective
end Whir.PublicCompressionCouplingBirthdayCache
