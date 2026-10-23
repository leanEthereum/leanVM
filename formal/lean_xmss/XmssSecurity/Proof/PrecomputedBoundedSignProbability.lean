import XmssSecurity.Proof.PrecomputedBoundedSignCache
import XmssSecurity.Proof.SignCacheHitProbability
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

noncomputable local instance precomputedRandomnessSampleable : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def Concrete.precomputedSignBoundedAttemptsContinuation
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness) (result : Option Signature × QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  match result.1 with
  | some signature => pure (some signature, result.2)
  | none => (simulateQ romImpl
      (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
        result.2

attribute [irreducible] Concrete.precomputedSignBoundedAttemptsContinuation

theorem Concrete.precomputedSignBoundedAttempts_run_succ_eq
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base (attempts + 1)
        trial)).run cache =
      ((simulateQ randomOracle
          (Concrete.precomputedSignAttempt secretKey leafIndex message
            (base + BitVec.ofNat randomnessBits trial) :
            OracleComp HashSpec (Option Signature))).run cache >>=
          Concrete.precomputedSignBoundedAttemptsContinuation attempts (trial + 1) secretKey
            leafIndex message base) := by
  rw [Concrete.precomputedSignBoundedAttempts, simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message
            (base + BitVec.ofNat randomnessBits trial) :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Concrete.precomputedSignAttempt secretKey leafIndex message
            (base + BitVec.ofNat randomnessBits trial) :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message
          (base + BitVec.ofNat randomnessBits trial) :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.precomputedSignAttempt secretKey leafIndex message
        (base + BitVec.ofNat randomnessBits trial) :
        OracleComp HashSpec (Option Signature))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result <;> simp [Concrete.precomputedSignBoundedAttemptsContinuation]

/-- A signature the scan returns uses one of its trials `base + c`. -/
theorem Concrete.precomputedSignBoundedAttempts_success_randomness
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness) (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
          initialCache)) :
    ∃ c, trial ≤ c ∧ c < trial + attempts ∧
      signature.randomness = base + BitVec.ofNat randomnessBits c := by
  induction attempts generalizing trial initialCache with
  | zero => simp [Concrete.precomputedSignBoundedAttempts] at hmem
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨⟨result, attemptCache⟩, hattempt, hcontinue⟩ := hmem
      cases result with
      | none =>
          obtain ⟨c, hlo, hhi, hc⟩ := ih (trial + 1) attemptCache (by
            simpa [Concrete.precomputedSignBoundedAttemptsContinuation] using hcontinue)
          exact ⟨c, by omega, by omega, hc⟩
      | some found =>
          have hfound : found = signature := by
            simpa [Concrete.precomputedSignBoundedAttemptsContinuation] using
              (congrArg Prod.fst (by
                simpa [Concrete.precomputedSignBoundedAttemptsContinuation] using hcontinue :
                  (some signature, finalCache) = (some found, attemptCache))).symm
          subst hfound
          exact ⟨trial, le_rfl, by omega,
            Concrete.precomputedSignAttempt_some_randomness secretKey leafIndex message _
              initialCache attemptCache found hattempt⟩

theorem probEvent_uniform_add_const (P : Randomness → Prop) (c : Randomness) :
    Pr{let base ← $ᵗ Randomness}[P (base + c)] =
      Pr{let x ← $ᵗ Randomness}[P x] := by
  have hbij : Function.Bijective (· + c : Randomness → Randomness) :=
    ⟨add_left_injective c, fun y => ⟨y - c, sub_add_cancel y c⟩⟩
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective hbij).prEvent_eq P
  rw [prEvent_map] at h
  exact h

set_option linter.constructorNameAsVariable false in
/-- The returned trial was already queried with probability at most `A_max` times the cached share. -/
theorem Concrete.precomputedCappedSign_encodingInput_initialCache_hit_le_cachedCount
    (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec) :
    Pr{let result ← ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey leafIndex message)).run cache)}[∃ signature, result.1 = some signature ∧ ∃ output,
        cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
          (message, signature.randomness)) = some output] ≤
      (signingAttemptLimit : ℝ≥0∞) *
        cachedEncodingEntryCount cache secretKey.parameter leafIndex *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, randomness)) =
      some output
  have hsample :
      (simulateQ romImpl (liftM Concrete.signingRandomness)).run cache =
        (fun base => (base, cache)) <$> Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run cache = _
    exact roSim.run_liftM (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness cache
  rw [Concrete.precomputedCappedSign, simulateQ_bind, StateT.run_bind, hsample,
    Concrete.signingRandomness_eq, bind_map_left]
  calc
    _ ≤ Pr{let base ← $ᵗ Randomness}[∃ c, c < signingAttemptLimit ∧ hit (base + BitVec.ofNat randomnessBits c)] := by
      refine (prEvent_bind_le_prEvent_add_of_support (ε := 0) _ _ _ _ ?_).trans (by rw [add_zero])
      intro base _ hbase
      refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)
      rintro ⟨result, resultCache⟩ hmem ⟨signature, hsignature, houtput⟩
      simp only at hsignature
      subst hsignature
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨inner, innerCache⟩, hmem, hreturn⟩ := hmem
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hreturn
      obtain ⟨hresult, rfl⟩ := hreturn
      have hinner : inner = some signature := by
        split at hresult
        · exact hresult.symm
        · simp at hresult
      subst hinner
      obtain ⟨c, -, hc, hrandomness⟩ :=
        Concrete.precomputedSignBoundedAttempts_success_randomness signingAttemptLimit 0
          secretKey leafIndex message base cache resultCache signature hmem
      rw [hrandomness] at houtput
      exact hbase ⟨c, by omega, houtput⟩
    _ ≤ ∑ c ∈ Finset.range signingAttemptLimit,
          Pr{let base ← $ᵗ Randomness}[hit (base + BitVec.ofNat randomnessBits c)] := by
      refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_exists_finset_le
        (Finset.range signingAttemptLimit) _ _)
      rintro base - ⟨c, hc, hhit⟩
      exact ⟨c, Finset.mem_range.mpr hc, hhit⟩
    _ = ∑ _c ∈ Finset.range signingAttemptLimit,
          Pr{let x ← $ᵗ Randomness}[hit x] := by
      apply Finset.sum_congr rfl
      intro c _
      exact probEvent_uniform_add_const hit _
    _ ≤ ∑ _c ∈ Finset.range signingAttemptLimit,
          cachedEncodingEntryCount cache secretKey.parameter leafIndex *
            ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact uniform_signingRandomness_encodingInput_cacheHit_le_cachedEncodingEntryCount
        secretKey.parameter leafIndex message cache
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

end XmssSecurity
