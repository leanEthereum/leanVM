import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestAttemptExpectation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix

private theorem probEvent_digestContinuation_prehit_eq
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message workingCache)) :
    Pr[PrehitSelectedView referenceCache key message P |
      signDigestLoopContinuation attempts key message result.1 result.2] =
      (if FavorablePrehitAttempt referenceCache key message P result then 1 else 0) +
        (if result.2.1 = none then Pr[PrehitSelectedView referenceCache key message P |
          (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0) := by
  cases hresult : result.2.1 with
  | none =>
      have hnot : ¬ FavorablePrehitAttempt referenceCache key message P result := by
        rintro ⟨output, hc, ha, _⟩
        have heq := signDigestAttemptPrefix_cached_result key message workingCache result output hr (hreference hc)
        exact ha (heq.symm.trans hresult)
      simp only [signDigestLoopContinuation, hresult, if_true, if_neg hnot, zero_add]
  | some selected =>
      obtain ⟨index, leaves⟩ := selected
      have hiff : PrehitSelectedView referenceCache key message P
          (some (result.1, index, leaves), result.2.2) ↔ FavorablePrehitAttempt referenceCache key message P result := by
        constructor
        · rintro ⟨randomness, foundIndex, foundLeaves, hfound, output, hc, ho, hP⟩
          have hfirst := congrArg Prod.fst (Option.some.inj hfound)
          refine ⟨output, ?_, ?_, hP⟩
          · rw [hfirst]
            exact hc
          · rw [ho]
            exact Option.some_ne_none _
        · rintro ⟨output, hc, _, hP⟩
          have heq := signDigestAttemptPrefix_cached_result key message workingCache result output hr (hreference hc)
          exact ⟨result.1, index, leaves, rfl, output, hc, heq.symm.trans hresult, hP⟩
      simp only [signDigestLoopContinuation, hresult, probEvent_pure, Option.some_ne_none, if_false, add_zero, hiff]

theorem probEvent_signDigestLoop_prehit_recurrence
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop (attempts + 1) key message)).run workingCache] =
      cachedDigestAttemptRate key message referenceCache P +
        ∑' result, Pr[= result | signDigestAttemptPrefix key message workingCache] *
          if result.2.1 = none then Pr[PrehitSelectedView referenceCache key message P |
            (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  rw [signDigestLoop_run_succ_eq_attemptPrefix, probEvent_bind_eq_tsum,
    ← probEvent_signDigestAttemptPrefix_favorablePrehit_eq referenceCache workingCache key message P,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support (signDigestAttemptPrefix key message workingCache)
  · rw [probEvent_digestContinuation_prehit_eq attempts key message referenceCache workingCache hreference P result hr]
    split_ifs <;> ring
  · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, ite_self, zero_add]

theorem probEvent_signDigestLoop_prehit_eq_rate_mul_attempts
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] =
      cachedDigestAttemptRate key message referenceCache P * digestAttemptExpectation attempts key message workingCache := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [signDigestLoop, PrehitSelectedView, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_prehit_recurrence attempts key message referenceCache workingCache hreference P,
        digestAttemptExpectation, mul_add, mul_one, ← ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support (signDigestAttemptPrefix key message workingCache)
      · by_cases hnone : result.2.1 = none
        · rw [if_pos hnone, if_pos hnone, ih result.2.2
            (hreference.trans (signDigestAttemptPrefix_cache_le key message workingCache result hr))]
          ring
        · simp only [if_neg hnone, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, mul_zero]

end SphincsSecurity.Concrete
