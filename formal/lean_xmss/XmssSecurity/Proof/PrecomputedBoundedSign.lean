import XmssSecurity.Proof.PrecomputedKeyConsistency

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.precomputedSignBoundedAttempts_success_origin
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
          initialCache)) :
    ∃ randomness attemptCache resultCache,
      (some signature, resultCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))).run attemptCache) ∧
      resultCache ≤ finalCache := by
  induction attempts generalizing trial initialCache finalCache signature with
  | zero =>
      simp [Concrete.precomputedSignBoundedAttempts] at hmem
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨result, resultCache⟩, hattempt, hcontinue⟩ := hmem
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
      cases result with
      | none =>
          exact ih (trial + 1) resultCache finalCache signature hcontinue
      | some found =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨hsignature, hcache⟩ := hcontinue
          have hsignature' : signature = found := Option.some.inj hsignature
          subst found
          subst finalCache
          exact ⟨randomness, initialCache, resultCache, hattempt, le_rfl⟩

theorem Concrete.precomputedSignBoundedAttempts_success_replay
    (attempts trial : Nat) (secretKey : SecretKey) (request : SignRequest) (base : Randomness)
    (keygenCache initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hconsistent : PrecomputedKeyConsistent keygenCache secretKey)
    (hkeygenLe : keygenCache ≤ largerCache)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey request.leafIndex
          request.message base attempts trial)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.leafIndex signature.randomness encoding := by
  obtain ⟨randomness, attemptCache, finalAttemptCache, hattempt, hattemptLe⟩ :=
    Concrete.precomputedSignBoundedAttempts_success_origin attempts trial secretKey
      request.leafIndex request.message base initialCache resultCache signature hmem
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey request.leafIndex request.message randomness :
      OracleComp HashSpec (Option Signature)) attemptCache finalAttemptCache largerCache
      (some signature) hattempt (hattemptLe.trans hle)
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  split at heval
  · rename_i _ encoding hdecode
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at heval
    have hrandomness : randomness = signature.randomness := by
      simpa only [Concrete.precomputedSignWithEncoding] using
        congrArg Signature.randomness heval
    refine ⟨encoding, ?_, ?_⟩
    · rw [← hrandomness]
      exact hdecode
    · rw [← hrandomness, ← heval]
      exact hconsistent largerCache hkeygenLe request.leafIndex randomness encoding
  · simp at heval

theorem Concrete.precomputedCappedSign_success_replay
    (secretKey : SecretKey) (request : SignRequest)
    (keygenCache initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hconsistent : PrecomputedKeyConsistent keygenCache secretKey)
    (hkeygenLe : keygenCache ≤ largerCache)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.leafIndex
          request.message)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.leafIndex signature.randomness encoding := by
  rw [Concrete.precomputedCappedSign, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨base, baseCache⟩, hbase, hrest⟩ := hmem
  have hbaseCache : baseCache = initialCache :=
    xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
      (base, baseCache) hbase
  subst baseCache
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨result, attemptsCache⟩, hattempts, hreturn⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hreturn
  obtain ⟨hresult, rfl⟩ := hreturn
  split at hresult
  · subst hresult
    exact Concrete.precomputedSignBoundedAttempts_success_replay signingAttemptLimit 0
      secretKey request base keygenCache initialCache resultCache largerCache signature
      hconsistent hkeygenLe hattempts hle
  · simp at hresult

end XmssSecurity
