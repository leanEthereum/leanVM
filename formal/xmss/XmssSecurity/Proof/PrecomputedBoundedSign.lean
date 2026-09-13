import XmssSecurity.Proof.PrecomputedKeyConsistency

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.precomputedSignBoundedAttempts_success_origin
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts attempts secretKey epoch message)).run
          initialCache)) :
    ∃ randomness attemptCache resultCache,
      (some signature, resultCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.precomputedSignAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run attemptCache) ∧
      resultCache ≤ finalCache := by
  induction attempts generalizing initialCache finalCache signature with
  | zero =>
      simp [Concrete.precomputedSignBoundedAttempts] at hmem
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hrest⟩ := hmem
      have hrandomnessCache : randomnessCache = initialCache :=
        xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
          (randomness, randomnessCache) hrandomness
      subst randomnessCache
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨result, resultCache⟩, hattempt, hcontinue⟩ := hrest
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
      cases result with
      | none =>
          exact ih resultCache finalCache signature hcontinue
      | some found =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨hsignature, hcache⟩ := hcontinue
          have hsignature' : signature = found := Option.some.inj hsignature
          subst found
          subst finalCache
          exact ⟨randomness, initialCache, resultCache, hattempt, le_rfl⟩

theorem Concrete.precomputedSignBoundedAttempts_success_replay
    (attempts : Nat) (secretKey : SecretKey) (request : SignRequest)
    (keygenCache initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hconsistent : PrecomputedKeyConsistent keygenCache secretKey)
    (hkeygenLe : keygenCache ≤ largerCache)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts attempts secretKey request.epoch
          request.message)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.epoch signature.randomness encoding := by
  obtain ⟨randomness, attemptCache, finalAttemptCache, hattempt, hattemptLe⟩ :=
    Concrete.precomputedSignBoundedAttempts_success_origin attempts secretKey
      request.epoch request.message initialCache resultCache signature hmem
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey request.epoch request.message randomness :
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
      exact hconsistent largerCache hkeygenLe request.epoch randomness encoding
  · simp at heval

theorem Concrete.precomputedCappedSign_success_replay
    (secretKey : SecretKey) (request : SignRequest)
    (keygenCache initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hconsistent : PrecomputedKeyConsistent keygenCache secretKey)
    (hkeygenLe : keygenCache ≤ largerCache)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.epoch
          request.message)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.epoch signature.randomness encoding := by
  rw [Concrete.precomputedCappedSign] at hmem
  exact Concrete.precomputedSignBoundedAttempts_success_replay signingAttemptLimit
    secretKey request keygenCache initialCache resultCache largerCache signature
    hconsistent hkeygenLe hmem hle

end XmssSecurity
