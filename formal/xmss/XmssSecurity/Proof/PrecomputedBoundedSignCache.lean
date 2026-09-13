import XmssSecurity.Proof.PrecomputedBoundedSign
import XmssSecurity.Proof.PrecomputedSignQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.precomputedSignAttempt_none_attemptedInput_ne_of_later_decode
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (none, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding) :
    Concrete.CacheView.encodingInput secretKey.parameter epoch (message, randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput := by
  intro heq
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)) initialCache resultCache largerCache none hmem hle
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  have hattemptDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter epoch
        (message, randomness)) = some encoding := by
    unfold Concrete.CacheView.encodingHash at hdecode ⊢
    rw [heq]
    exact hdecode
  rw [hattemptDecode] at heval
  cases heval

theorem Concrete.precomputedSignAttempt_none_preserves_later_valid_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (none, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    initialCache resultCache none
  · exact Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
      secretKey epoch targetEpoch message randomness targetInput
        (Concrete.precomputedSignAttempt_none_attemptedInput_ne_of_later_decode secretKey
          epoch targetEpoch message randomness targetInput initialCache resultCache largerCache
          hmem hle encoding hdecode)
  · exact hnone
  · exact hmem

theorem Concrete.precomputedSignAttempt_some_randomness
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (initialCache resultCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache)) :
    signature.randomness = randomness := by
  have heval := Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)) initialCache resultCache (some signature) hmem
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  split at heval
  · simp only [evalWithAnswerFn_pure, Option.some.injEq] at heval
    simpa only [Concrete.precomputedSignWithEncoding] using
      congrArg Signature.randomness heval.symm
  · simp at heval

theorem Concrete.precomputedSignAttempt_some_preserves_other_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hne : Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, signature.randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  have hrandomness := Concrete.precomputedSignAttempt_some_randomness secretKey epoch message
    randomness initialCache resultCache signature hmem
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.precomputedSignAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    initialCache resultCache (some signature)
  · apply Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
    simpa [hrandomness] using hne
  · exact hnone
  · exact hmem

theorem Concrete.precomputedSignBoundedAttempts_preserves_later_valid_other_encodingInput
    (attempts : Nat) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts attempts secretKey epoch message)).run
          initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding)
    (hother : ∀ signature, result = some signature →
      Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  induction attempts generalizing initialCache resultCache result with
  | zero =>
      simp only [Concrete.precomputedSignBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, hcache⟩ := hmem
      subst resultCache
      exact hnone
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hrest⟩ := hmem
      have hrandomnessCache : randomnessCache = initialCache :=
        xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
          (randomness, randomnessCache) hrandomness
      subst randomnessCache
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hrest
      have hroute :
          simulateQ romImpl
              (liftM (Concrete.precomputedSignAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature))) =
            simulateQ randomOracle
              (Concrete.precomputedSignAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature)) := by
        change simulateQ (unifFwdImpl HashSpec + randomOracle)
            (liftM (Concrete.precomputedSignAttempt secretKey epoch message randomness :
              OracleComp HashSpec (Option Signature))) = _
        exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.precomputedSignAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))
      rw [hroute] at hattempt
      cases attemptResult with
      | none =>
          have hattemptLeResult : attemptCache ≤ resultCache :=
            xmssRom_cache_le
              (Concrete.precomputedSignBoundedAttempts attempts secretKey epoch message)
              attemptCache (result, resultCache) hcontinue
          have hattemptNone :=
            Concrete.precomputedSignAttempt_none_preserves_later_valid_encodingInput
              secretKey epoch targetEpoch message randomness targetInput initialCache
              attemptCache largerCache hattempt (hattemptLeResult.trans hle) encoding hdecode
              hnone
          exact ih attemptCache resultCache result hcontinue hle hother hattemptNone
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨hresult, hcache⟩ := hcontinue
          have hsignature : result = some signature := hresult
          subst resultCache
          exact Concrete.precomputedSignAttempt_some_preserves_other_encodingInput
            secretKey epoch targetEpoch message randomness targetInput initialCache
            attemptCache signature hattempt (hother signature hsignature) hnone

theorem Concrete.precomputedCappedSign_preserves_later_valid_other_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey epoch message)).run initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding)
    (hother : ∀ signature, result = some signature →
      Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  rw [Concrete.precomputedCappedSign] at hmem
  exact Concrete.precomputedSignBoundedAttempts_preserves_later_valid_other_encodingInput
    signingAttemptLimit secretKey epoch targetEpoch message targetInput initialCache resultCache
    largerCache result hmem hle encoding hdecode hother hnone

theorem Concrete.precomputedSignBoundedAttempts_preserves_other_epoch_encodingInput
    (attempts : Nat) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts attempts secretKey epoch message)).run
          initialCache))
    (hne : epoch ≠ targetEpoch)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  induction attempts generalizing initialCache finalCache result with
  | zero =>
      simp only [Concrete.precomputedSignBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, hcache⟩ := hmem
      subst finalCache
      exact hnone
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hrest⟩ := hmem
      have hrandomnessCache : randomnessCache = initialCache :=
        xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
          (randomness, randomnessCache) hrandomness
      subst randomnessCache
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hrest
      have hroute :
          simulateQ romImpl
              (liftM (Concrete.precomputedSignAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature))) =
            simulateQ randomOracle
              (Concrete.precomputedSignAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature)) := by
        change simulateQ (unifFwdImpl HashSpec + randomOracle)
            (liftM (Concrete.precomputedSignAttempt secretKey epoch message randomness :
              OracleComp HashSpec (Option Signature))) = _
        exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.precomputedSignAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))
      rw [hroute] at hattempt
      have hattemptNone : attemptCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) =
            none := by
        apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.precomputedSignAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
          initialCache attemptCache attemptResult
        · apply Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
          intro heq
          exact hne (Concrete.CacheView.epoch_eq_of_encodingInput_eq
            secretKey.parameter heq)
        · exact hnone
        · exact hattempt
      cases attemptResult with
      | none => exact ih attemptCache finalCache result hcontinue hattemptNone
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨_, hcache⟩ := hcontinue
          subst finalCache
          exact hattemptNone

theorem Concrete.precomputedCappedSign_preserves_other_epoch_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey epoch message)).run initialCache))
    (hne : epoch ≠ targetEpoch)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  rw [Concrete.precomputedCappedSign] at hmem
  exact Concrete.precomputedSignBoundedAttempts_preserves_other_epoch_encodingInput
    signingAttemptLimit secretKey epoch targetEpoch message targetInput initialCache finalCache
    result hmem hne hnone

theorem Concrete.precomputedCappedSign_success_decode
    (secretKey : SecretKey) (request : SignRequest)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.epoch
          request.message)).run initialCache)) :
    ∃ encoding, TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some encoding := by
  obtain ⟨randomness, attemptCache, resultCache, hattempt, hle⟩ :=
    Concrete.precomputedSignBoundedAttempts_success_origin signingAttemptLimit secretKey
      request.epoch request.message initialCache finalCache signature (by
        rw [← Concrete.precomputedCappedSign]
        exact hmem)
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey request.epoch request.message randomness :
      OracleComp HashSpec (Option Signature)) attemptCache resultCache finalCache
      (some signature) hattempt hle
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  split at heval
  · rename_i _ encoding hdecode
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at heval
    have hrandomness : randomness = signature.randomness := by
      simpa only [Concrete.precomputedSignWithEncoding] using
        congrArg Signature.randomness heval
    exact ⟨encoding, by simpa only [hrandomness] using hdecode⟩
  · simp at heval

theorem Concrete.precomputedCappedSign_success_encodingInput_cached
    (secretKey : SecretKey)
    (request : SignRequest) (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.epoch
          request.message)).run initialCache)) :
    ∃ output, finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some output := by
  obtain ⟨encoding, hdecode⟩ :=
    Concrete.precomputedCappedSign_success_decode secretKey request
      initialCache finalCache signature hmem
  exact Concrete.CacheView.encodingInput_cached_of_decode_some finalCache
    secretKey.parameter request.epoch request.message signature.randomness encoding hdecode

end XmssSecurity
