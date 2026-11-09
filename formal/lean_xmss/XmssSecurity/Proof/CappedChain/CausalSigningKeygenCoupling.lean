module

public import XmssSecurity.Proof.CacheAgreement
public import XmssSecurity.Proof.ChainWalkCache
public import XmssSecurity.Proof.BoundedSignProbability
public import XmssSecurity.Proof.PrecomputedBoundedSignProbability
public import XmssSecurity.Proof.CappedChain.TreeCacheStable
public import XmssSecurity.Proof.CausalTreeCoupling
public import XmssSecurity.Proof.KeygenCache
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem simulate_sequenceFin_run_eq_pure
    {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (values : Fin n → α)
    (hrun : ∀ index,
      (simulateQ randomOracle (computation index)).run cache =
        pure (values index, cache)) :
    (simulateQ randomOracle (Concrete.sequenceFin computation)).run cache =
      pure (values, cache) := by
  induction n with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → α) = values := by
        funext index
        exact Fin.elim0 index
      simp [Concrete.sequenceFin, hvalues]
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind, hrun 0]
      simp only [pure_bind]
      rw [simulateQ_bind, StateT.run_bind,
        ih (fun index => computation index.succ)
          (fun index => values index.succ) (fun index => hrun index.succ)]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      congr
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

theorem Concrete.keygen_signedChainValues_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (encoding : Encoding) :
    (simulateQ randomOracle
      (Concrete.signedChainValues keyResult.1.2 leafIndex encoding)).run
        largerCache =
      pure (Concrete.CacheReplay.signedChainValues largerCache
        keyResult.1.2 leafIndex encoding, largerCache) := by
  let values : ChainIndex → Digest := fun chain =>
    keygenChainValueTable keyResult.2 keyResult.1.2 chain
      (.inl leafIndex, encoding chain)
  have hrun : ∀ chain,
      (simulateQ randomOracle
        (Concrete.chainWalk keyResult.1.2.parameter leafIndex chain 0
          (encoding chain).val
          (keyResult.1.2.chainStart leafIndex chain))).run largerCache =
        pure (values chain, largerCache) := by
    intro chain
    exact simulate_chainWalk_run_eq_pure_of_table_matches largerCache
      keyResult.1.2 chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain)
      (keygenChainValueTable_seedsMatch keyResult.2 keyResult.1.2 chain)
      ((Concrete.keygenChainValueTable_edgesMatch
        keyResult hkeyResult chain).mono hle)
      leafIndex (encoding chain).val (encoding chain).isLt
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun chain => Concrete.chainWalk keyResult.1.2.parameter leafIndex chain 0
      (encoding chain).val (keyResult.1.2.chainStart leafIndex chain))
    largerCache values hrun
  have hvalues : values = Concrete.CacheReplay.signedChainValues
      largerCache keyResult.1.2 leafIndex encoding := by
    funext chain
    exact Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeyResult
      largerCache hle (.inl leafIndex) chain (encoding chain).val
        (Nat.le_pred_of_lt (encoding chain).isLt)
  simpa [Concrete.signedChainValues, hvalues] using hsequence

theorem TreeCacheStable.authenticationPath_run_eq_pure
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (leafIndex : LeafIndex) :
    (simulateQ randomOracle
      (Concrete.authenticationPath secretKey leafIndex)).run largerCache =
      pure (Concrete.CacheReplay.authenticationPath largerCache secretKey leafIndex,
        largerCache) := by
  have hrun : ∀ level,
      (simulateQ randomOracle
        (Concrete.treeNode secretKey.parameter secretKey.chainStart level.val
          (Concrete.authenticationPathNode leafIndex level) :
          OracleComp HashSpec Digest)).run largerCache =
        pure (Concrete.CacheReplay.treeNode cache secretKey.parameter
          secretKey.chainStart level.val
            (Concrete.authenticationPathNode leafIndex level), largerCache) := by
    intro level
    exact hstable level.val (Concrete.authenticationPathNode leafIndex level)
      (by omega) (authenticationPathNode_subtreeValid leafIndex level)
        largerCache hle
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun level => Concrete.treeNode secretKey.parameter secretKey.chainStart
      level.val (Concrete.authenticationPathNode leafIndex level)) largerCache
    (Concrete.CacheReplay.authenticationPath cache secretKey leafIndex) hrun
  rw [hstable.authenticationPath_eq secretKey cache largerCache hle leafIndex]
    at hsequence
  simpa [Concrete.authenticationPath] using hsequence

theorem topPathNode_val_lt (key : TopIndex) (level : MerkleLevel) :
    (Concrete.topPathNode key level).val < 2 ^ (treeHeight - level.val) := by
  have hkey := key.isLt
  have hlevel := level.isLt
  simp only [topLifetime, treeHeight] at hkey hlevel ⊢
  have hdiv : key.val / 2 ^ level.val < 2 ^ (16 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _), ← pow_add, Nat.sub_add_cancel hlevel.le]
    exact hkey
  have hxor : Nat.xor (key.val / 2 ^ level.val) 1 < 2 ^ (16 - level.val) :=
    Nat.xor_lt_two_pow hdiv (Nat.one_lt_two_pow (by omega))
  unfold Concrete.topPathNode Concrete.topNodeOfNat
  simp only [topLifetime, treeHeight]
  rw [Nat.mod_eq_of_lt (hxor.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))]
  exact hxor

attribute [local irreducible] Concrete.topTreeNode in
/-- Key generation's cache answers the honest top signature without a fresh query. -/
theorem Concrete.keygen_topSignature_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache) (key : TopIndex) :
    (simulateQ randomOracle (Concrete.topSignature keyResult.1.2 key)).run largerCache =
      pure (Concrete.CacheReplay.topPartFromCache largerCache keyResult.1.2 key, largerCache) := by
  obtain ⟨parameter, secret, topSecret, topBase, result, hkey, hrun⟩ :=
    Concrete.keygen_support_rootTree keyResult hkeyResult
  have hsk : keyResult.1.2 = SecretKey.withoutPrecomputation parameter secret topSecret result.2 :=
    congrArg Prod.snd hkey
  rw [hsk]
  unfold Concrete.topSignature Concrete.CacheReplay.topPartFromCache
  change (simulateQ randomOracle (match result.2 key with
    | some (randomness, encoding) => do
        let chainValue ← Concrete.sequenceFin fun chain =>
          Concrete.topChainWalk parameter key chain 0 (encoding chain).val (topSecret key chain)
        let authPath ← Concrete.sequenceFin fun level : Fin treeHeight =>
          Concrete.topTreeNode parameter topSecret level.val (Concrete.topPathNode key level)
        return ⟨randomness, chainValue, authPath⟩
    | none => pure ⟨0, fun _ => 0, fun _ => 0⟩ : OracleComp HashSpec LayerSignature)).run
      largerCache = pure (match result.2 key with
    | some (randomness, encoding) =>
        ⟨randomness, Concrete.honestTopValues largerCache
          (SecretKey.withoutPrecomputation parameter secret topSecret result.2) key encoding,
          fun level => Concrete.honestTopPath largerCache
            (SecretKey.withoutPrecomputation parameter secret topSecret result.2) key level.val⟩
    | none => ⟨0, fun _ => 0, fun _ => 0⟩, largerCache)
  cases result.2 key with
  | none => simp
  | some signed =>
      obtain ⟨randomness, encoding⟩ := signed
      simp only
      rw [simulateQ_bind, StateT.run_bind, sequenceFin_run_eq_pure _ largerCache
        (Concrete.honestTopValues largerCache
          (SecretKey.withoutPrecomputation parameter secret topSecret result.2) key encoding)]
      · simp only [pure_bind]
        rw [simulateQ_bind, StateT.run_bind, sequenceFin_run_eq_pure _ largerCache
          (fun level : Fin treeHeight => Concrete.honestTopPath largerCache
            (SecretKey.withoutPrecomputation parameter secret topSecret result.2) key level.val)]
        · simp
        · intro level
          have hrb := Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hrun level.val
            (Concrete.topPathNode key level) level.isLt.le (topPathNode_val_lt key level)
          rw [hrb.run_eq largerCache hle, hrb.eval_eq largerCache hle,
            Concrete.CacheReplay.eval_topTreeNode]
          simp [Concrete.honestTopPath, level.isLt, SecretKey.withoutPrecomputation]
      · intro chain
        have hrb := Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk hrun key chain (encoding chain).val
          (Nat.le_pred_of_lt (encoding chain).isLt)
        rw [hrb.run_eq largerCache hle, hrb.eval_eq largerCache hle,
          Concrete.CacheReplay.eval_topChainWalk]
        rfl

theorem Concrete.keygen_signWithEncoding_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) :
    (simulateQ randomOracle
      (Concrete.signWithEncoding keyResult.1.2 leafIndex randomness encoding)).run
        largerCache =
      pure (Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        leafIndex randomness encoding, largerCache) := by
  unfold Concrete.signWithEncoding
  rw [simulateQ_bind, StateT.run_bind,
    Concrete.keygen_signedChainValues_run_eq_pure keyResult hkeyResult
      largerCache hle leafIndex encoding]
  simp only [pure_bind]
  rw [simulateQ_bind, StateT.run_bind,
    hstable.authenticationPath_run_eq_pure keyResult.1.2 keyResult.2
      largerCache hle leafIndex]
  simp only [pure_bind]
  rw [simulateQ_bind, StateT.run_bind,
    Concrete.keygen_topSignature_run_eq_pure keyResult hkeyResult largerCache hle]
  simp [Concrete.CacheReplay.signWithEncoding]

theorem Concrete.precomputedSignAttempt_materialized_run_eq_signAttempt
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    ((simulateQ randomOracle
      (Concrete.precomputedSignAttempt
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          leafIndex message randomness : OracleComp HashSpec (Option Signature))).run
        largerCache) =ᵈ
      ((simulateQ randomOracle
        (Concrete.signAttempt keyResult.1.2 leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run largerCache) := by
  have hmaterialized :=
    Concrete.oldKeygen_support_materializedPrecomputedKeygen keyResult hkeyResult
  have hconsistent := Concrete.precomputedKeygen_support_consistent
    (Concrete.materializeCachedKeyResult keyResult) hmaterialized
  unfold Concrete.precomputedSignAttempt Concrete.signAttempt
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [Concrete.materializePrecomputation,
    Concrete.precomputedSecretKey]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro digestResult hdigestResult
  have hdigestLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.encodingHash keyResult.1.2.parameter leafIndex message randomness)
      largerCache digestResult (by
        simpa [Concrete.materializePrecomputation] using hdigestResult)
  cases hdecode : TargetSum.decodeDigest digestResult.1 with
  | none =>
    simp only
    rfl
  | some encoding =>
    simp only
    rw [simulateQ_map, StateT.run_map]
    rw [Concrete.keygen_signWithEncoding_run_eq_pure keyResult hkeyResult
      hstable digestResult.2 (hle.trans hdigestLe)
      leafIndex randomness encoding]
    simp only [Functor.map]
    have hsignature := hconsistent digestResult.2 (hle.trans hdigestLe)
      leafIndex randomness encoding
    change Concrete.precomputedSignWithEncoding
      (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
        leafIndex randomness encoding =
      Concrete.CacheReplay.signWithEncoding digestResult.2 keyResult.1.2
        leafIndex randomness encoding at hsignature
    simp only [Concrete.materializePrecomputation,
      Concrete.precomputedSecretKey] at hsignature
    rw [hsignature]
    rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem Concrete.evalDist_precomputedSignBoundedAttempts_materialized_eq
    (attempts trial : Nat) (base : Randomness)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (message : Message) :
    ((simulateQ romImpl
      (Concrete.precomputedSignBoundedAttempts
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          leafIndex message base attempts trial)).run largerCache) =ᵈ
      ((simulateQ romImpl
        (Concrete.signBoundedAttempts keyResult.1.2 leafIndex message base attempts trial)).run
          largerCache) := by
  induction attempts generalizing trial largerCache with
  | zero => rfl
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq,
        Concrete.signBoundedAttempts_run_succ_eq]
      set randomness := base + BitVec.ofNat randomnessBits trial
      calc
        ((simulateQ randomOracle
              (Concrete.precomputedSignAttempt
                (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                  leafIndex message randomness :
                    OracleComp HashSpec (Option Signature))).run largerCache >>=
            Concrete.precomputedSignBoundedAttemptsContinuation attempts (trial + 1)
              (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                leafIndex message base) =ᵈ
            ((simulateQ randomOracle
              (Concrete.signAttempt keyResult.1.2 leafIndex message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Concrete.precomputedSignBoundedAttemptsContinuation attempts (trial + 1)
                (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
                  leafIndex message base) :=
          (Concrete.precomputedSignAttempt_materialized_run_eq_signAttempt
              keyResult hkeyResult hstable largerCache hle leafIndex message randomness).bind_left _
        _ =ᵈ ((simulateQ randomOracle
              (Concrete.signAttempt keyResult.1.2 leafIndex message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Concrete.signBoundedAttemptsContinuation attempts (trial + 1) keyResult.1.2
                leafIndex message base) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro result hresult
          cases hoption : result.1 with
          | none =>
              simp only [Concrete.precomputedSignBoundedAttemptsContinuation,
                Concrete.signBoundedAttemptsContinuation]
              rw [hoption]
              apply ih (trial + 1) result.2
              exact hle.trans (Concrete.CacheReplay.randomOracle_cache_le
                (Concrete.signAttempt keyResult.1.2 leafIndex message randomness :
                  OracleComp HashSpec (Option Signature)) largerCache result hresult)
          | some signature =>
              simp only [Concrete.precomputedSignBoundedAttemptsContinuation,
                Concrete.signBoundedAttemptsContinuation]
              rw [hoption]

theorem Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (message : Message) :
    ((simulateQ romImpl
      (Concrete.precomputedCappedSign
        (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
          leafIndex message)).run largerCache) =ᵈ
      ((simulateQ romImpl
        (Concrete.cappedSign keyResult.1.2 leafIndex message)).run
          largerCache) := by
  rw [Concrete.precomputedCappedSign, Concrete.cappedSign_eq, simulateQ_bind, StateT.run_bind,
    simulateQ_bind, StateT.run_bind]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro sampled hsampled
  have hcache : sampled.2 = largerCache :=
    xmssRom_lift_probComp_cache_eq Concrete.signingRandomness largerCache sampled hsampled
  rw [hcache]
  have htop : Concrete.topSignedAt (Concrete.materializePrecomputation keyResult.2 keyResult.1.2)
      leafIndex = Concrete.topSignedAt keyResult.1.2 leafIndex := rfl
  rw [htop, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  exact (Concrete.evalDist_precomputedSignBoundedAttempts_materialized_eq
    signingAttemptLimit 0 sampled.1 keyResult hkeyResult hstable largerCache hle leafIndex
      message).bind_left _

end XmssSecurity.CappedChain
