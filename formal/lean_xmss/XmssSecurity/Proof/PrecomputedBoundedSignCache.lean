import XmssSecurity.Proof.PrecomputedBoundedSign
import XmssSecurity.Proof.PrecomputedSignQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.precomputedSignAttempt_none_attemptedInput_ne_of_later_decode
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (none, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetLeafIndex
        targetInput) = some encoding) :
    Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput := by
  intro heq
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) initialCache resultCache largerCache none hmem hle
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  have hattemptDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter leafIndex
        (message, randomness)) = some encoding := by
    unfold Concrete.CacheView.encodingHash at hdecode ⊢
    rw [heq]
    exact hdecode
  rw [hattemptDecode] at heval
  cases heval

theorem Concrete.precomputedSignAttempt_none_preserves_later_valid_encodingInput
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (none, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetLeafIndex
        targetInput) = some encoding)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput)
    initialCache resultCache none
  · exact Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
      secretKey leafIndex targetLeafIndex message randomness targetInput
        (Concrete.precomputedSignAttempt_none_attemptedInput_ne_of_later_decode secretKey
          leafIndex targetLeafIndex message randomness targetInput initialCache resultCache largerCache
          hmem hle encoding hdecode)
  · exact hnone
  · exact hmem

theorem Concrete.precomputedSignAttempt_some_randomness
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (initialCache resultCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache)) :
    signature.randomness = randomness := by
  have heval := Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) initialCache resultCache (some signature) hmem
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  split at heval
  · simp only [evalWithAnswerFn_pure, Option.some.injEq] at heval
    simpa only [Concrete.precomputedSignWithEncoding] using
      congrArg Signature.randomness heval.symm
  · simp at heval

theorem Concrete.precomputedSignAttempt_some_preserves_other_encodingInput
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hne : Concrete.CacheView.encodingInput secretKey.parameter leafIndex
        (message, signature.randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none := by
  have hrandomness := Concrete.precomputedSignAttempt_some_randomness secretKey leafIndex message
    randomness initialCache resultCache signature hmem
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput)
    initialCache resultCache (some signature)
  · apply Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
    simpa [hrandomness] using hne
  · exact hnone
  · exact hmem

theorem Concrete.precomputedSignBoundedAttempts_preserves_later_valid_other_encodingInput
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (base : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
          initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetLeafIndex
        targetInput) = some encoding)
    (hother : ∀ signature, result = some signature →
      Concrete.CacheView.encodingInput secretKey.parameter leafIndex
          (message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none := by
  induction attempts generalizing trial initialCache resultCache result with
  | zero =>
      simp only [Concrete.precomputedSignBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, hcache⟩ := hmem
      subst resultCache
      exact hnone
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hmem
      set randomness := base + BitVec.ofNat randomnessBits trial
      have hroute :
          simulateQ romImpl
              (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Signature))) =
            simulateQ randomOracle
              (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Signature)) := by
        change simulateQ (unifFwdImpl HashSpec + randomOracle)
            (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
              OracleComp HashSpec (Option Signature))) = _
        exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))
      rw [hroute] at hattempt
      cases attemptResult with
      | none =>
          have hattemptLeResult : attemptCache ≤ resultCache :=
            xmssRom_cache_le
              (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts
                (trial + 1))
              attemptCache (result, resultCache) hcontinue
          have hattemptNone :=
            Concrete.precomputedSignAttempt_none_preserves_later_valid_encodingInput
              secretKey leafIndex targetLeafIndex message randomness targetInput initialCache
              attemptCache largerCache hattempt (hattemptLeResult.trans hle) encoding hdecode
              hnone
          exact ih (trial + 1) attemptCache resultCache result hcontinue hle hother hattemptNone
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨hresult, hcache⟩ := hcontinue
          have hsignature : result = some signature := hresult
          subst resultCache
          exact Concrete.precomputedSignAttempt_some_preserves_other_encodingInput
            secretKey leafIndex targetLeafIndex message randomness targetInput initialCache
            attemptCache signature hattempt (hother signature hsignature) hnone

theorem Concrete.precomputedCappedSign_preserves_later_valid_other_encodingInput
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey leafIndex message)).run initialCache))
    (hle : resultCache ≤ largerCache) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetLeafIndex
        targetInput) = some encoding)
    (hother : ∀ signature, result = some signature →
      Concrete.CacheView.encodingInput secretKey.parameter leafIndex
          (message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none)
    (hsuccess : result.isSome) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none := by
  rw [Concrete.precomputedCappedSign, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨base, baseCache⟩, hbase, hmem⟩ := hmem
  have hbaseCache : baseCache = initialCache :=
    xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache (base, baseCache) hbase
  subst baseCache
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨inner, innerCache⟩, hmem, hreturn⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hreturn
  obtain ⟨hresult, rfl⟩ := hreturn
  split at hresult
  · subst hresult
    exact Concrete.precomputedSignBoundedAttempts_preserves_later_valid_other_encodingInput
      signingAttemptLimit 0 secretKey leafIndex targetLeafIndex message base targetInput
      initialCache resultCache largerCache result hmem hle encoding hdecode hother hnone
  · subst hresult
    simp at hsuccess

theorem Concrete.precomputedSignBoundedAttempts_preserves_other_leafIndex_encodingInput
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (base : Randomness) (targetInput : Message × Randomness)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
          initialCache))
    (hne : leafIndex ≠ targetLeafIndex)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none := by
  induction attempts generalizing trial initialCache finalCache result with
  | zero =>
      simp only [Concrete.precomputedSignBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, hcache⟩ := hmem
      subst finalCache
      exact hnone
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hmem
      set randomness := base + BitVec.ofNat randomnessBits trial
      have hroute :
          simulateQ romImpl
              (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Signature))) =
            simulateQ randomOracle
              (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Signature)) := by
        change simulateQ (unifFwdImpl HashSpec + randomOracle)
            (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
              OracleComp HashSpec (Option Signature))) = _
        exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))
      rw [hroute] at hattempt
      have hattemptNone : attemptCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) =
            none := by
        apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))
          (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput)
          initialCache attemptCache attemptResult
        · apply Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
          intro heq
          exact hne (Concrete.CacheView.leafIndex_eq_of_encodingInput_eq
            secretKey.parameter heq)
        · exact hnone
        · exact hattempt
      cases attemptResult with
      | none => exact ih (trial + 1) attemptCache finalCache result hcontinue hattemptNone
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨_, hcache⟩ := hcontinue
          subst finalCache
          exact hattemptNone

theorem Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey leafIndex message)).run initialCache))
    (hne : leafIndex ≠ targetLeafIndex)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none := by
  rw [Concrete.precomputedCappedSign, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨base, baseCache⟩, hbase, hmem⟩ := hmem
  have hbaseCache : baseCache = initialCache :=
    xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache (base, baseCache) hbase
  subst baseCache
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨inner, innerCache⟩, hmem, hreturn⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hreturn
  obtain ⟨hresult, rfl⟩ := hreturn
  exact Concrete.precomputedSignBoundedAttempts_preserves_other_leafIndex_encodingInput
    signingAttemptLimit 0 secretKey leafIndex targetLeafIndex message base targetInput initialCache
    finalCache inner hmem hne hnone

theorem Concrete.precomputedCappedSign_success_decode
    (secretKey : SecretKey) (request : SignRequest)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.leafIndex
          request.message)).run initialCache)) :
    ∃ encoding, TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache secretKey.parameter request.leafIndex
        (request.message, signature.randomness)) = some encoding := by
  rw [Concrete.precomputedCappedSign, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨base, baseCache⟩, hbase, hmem⟩ := hmem
  have hbaseCache : baseCache = initialCache :=
    xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache (base, baseCache) hbase
  subst baseCache
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨inner, innerCache⟩, hmem, hreturn⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hreturn
  obtain ⟨hresult, rfl⟩ := hreturn
  split at hresult
  · subst hresult
    obtain ⟨randomness, attemptCache, resultCache, hattempt, hle⟩ :=
      Concrete.precomputedSignBoundedAttempts_success_origin signingAttemptLimit 0 secretKey
        request.leafIndex request.message base initialCache finalCache signature hmem
    have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.precomputedSignAttempt secretKey request.leafIndex request.message randomness :
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
  · simp at hresult

theorem Concrete.precomputedCappedSign_success_encodingInput_cached
    (secretKey : SecretKey)
    (request : SignRequest) (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.leafIndex
          request.message)).run initialCache)) :
    ∃ output, finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter request.leafIndex
        (request.message, signature.randomness)) = some output := by
  obtain ⟨encoding, hdecode⟩ :=
    Concrete.precomputedCappedSign_success_decode secretKey request
      initialCache finalCache signature hmem
  exact Concrete.CacheView.encodingInput_cached_of_decode_some finalCache
    secretKey.parameter request.leafIndex request.message signature.randomness encoding hdecode

end XmssSecurity
