import XmssSecurity.Proof.CappedChain.TreeCacheStable
import XmssSecurity.Proof.MerkleQueryPresence
import XmssSecurity.Proof.PrecomputedKeygenCache

open OracleComp OracleSpec

namespace XmssSecurity

def PrecomputedKeyConsistent (keygenCache : QueryCache HashSpec)
    (secretKey : SecretKey) : Prop :=
  ∀ largerCache, keygenCache ≤ largerCache →
    ∀ leafIndex randomness encoding,
      Concrete.precomputedSignWithEncoding secretKey leafIndex randomness encoding =
        Concrete.CacheReplay.signWithEncoding largerCache secretKey leafIndex randomness encoding

theorem Concrete.precomputedKeygen_support_oldKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2) ∈
      support ((simulateQ romImpl Concrete.keygen).run ∅) := by
  have hmapped : ((Concrete.erasePrecomputedKeyResult keyResult.1, keyResult.2)) ∈
      support ((simulateQ romImpl
        (Concrete.erasePrecomputedKeyResult <$> Concrete.precomputedKeygen)).run ∅) := by
    rw [simulateQ_map, StateT.run_map, support_map]
    exact ⟨keyResult, hmem, rfl⟩
  rw [Concrete.erasePrecomputedKeygen_eq_keygen] at hmapped
  exact hmapped

theorem Concrete.oldKeygen_support_materializedPrecomputedKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    Concrete.materializeCachedKeyResult keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
  rw [← OracleComp.support_eq_of_evalDistEq
    Concrete.evalDist_materialized_keygen_eq_precomputedKeygen]

  rw [support_map]
  exact ⟨keyResult, hmem, rfl⟩

theorem Concrete.precomputedKeygen_support_secretKey_components
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ∃ parameter secret topSecret topSigned,
      keyResult.1.2 = Concrete.precomputedSecretKey parameter secret topSecret topSigned keyResult.2 := by
  unfold Concrete.precomputedKeygen at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨secret, secretCache⟩, hsecret, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨topSecret, topSecretCache⟩, htopSecret, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨topBase, topBaseCache⟩, htopBase, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨result, resultCache⟩, hresult, hout⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  subst keyResult
  have h1 : parameterCache = ∅ :=
    xmssRom_lift_probComp_cache_eq Concrete.samplePublicParameter ∅ (parameter, parameterCache) hparameter
  have h2 : secretCache = parameterCache :=
    xmssRom_lift_probComp_cache_eq Concrete.sampleSecret parameterCache (secret, secretCache) hsecret
  have h3 : topSecretCache = secretCache :=
    xmssRom_lift_probComp_cache_eq Concrete.sampleTopSecret secretCache (topSecret, topSecretCache)
      htopSecret
  have h4 : topBaseCache = topSecretCache :=
    xmssRom_lift_probComp_cache_eq Concrete.sampleTopBase topSecretCache (topBase, topBaseCache) htopBase
  let honest : OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
    Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key))
  have hroute :
      simulateQ romImpl (liftM honest.withQueryLog) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          honest.withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) honest.withQueryLog
  rw [hroute, h4, h3, h2, h1] at hresult
  have hcache := hashCacheOfLog_eq_finalCache_of_empty honest (result, resultCache) hresult
  exact ⟨parameter, secret, topSecret, result.1.2, by simp only; rw [hcache]⟩
/-- Every bottom chain walk from its start ran inside key generation. -/
theorem Concrete.keygen_runsBelow_chainWalk
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    Concrete.CacheReplay.RunsBelow
      (Concrete.chainWalk keyResult.1.2.parameter leafIndex chain 0 steps
        (keyResult.1.2.chainStart leafIndex chain) : OracleComp HashSpec Digest) keyResult.2 := by
  obtain ⟨parameter, secret, topSecret, topBase, result, hkey, hresult⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.honestKeygen_runsBelow_chainWalk hresult leafIndex chain steps hsteps

/-- A chain step's input is cached by every run of the walk through it. -/
theorem Concrete.CacheReplay.RunsBelow.chainInput_cached {parameter : PublicParameter}
    {leafIndex : LeafIndex} {chain : ChainIndex} {value : Digest} {cache : QueryCache HashSpec}
    (step : ChainStep)
    (hrun : Concrete.CacheReplay.RunsBelow
      (Concrete.chainWalk parameter leafIndex chain 0 (step.val + 1) value :
        OracleComp HashSpec Digest) cache) :
    ∃ output, cache
      (Concrete.CacheView.chainInput parameter leafIndex chain step
        (Wots.walk (Concrete.CacheView.chainStep cache parameter leafIndex chain)
          0 step.val value)) = some output := by
  obtain ⟨beforeCache, afterCache, digest, hmem, hafter⟩ := hrun
  rw [Concrete.chainWalk] at hmem
  obtain ⟨previous, middleCache, hprevious, hrest, hmiddleLe⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hmem
  have hstep : 0 + step.val < chainLength - 1 := by simp
  simp only [hstep, ↓reduceDIte] at hrest
  obtain ⟨output, hcached, _⟩ := Concrete.CacheReplay.tweakableHash_query_cached parameter _ _
    middleCache afterCache digest hrest
  have hwalk := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.chainWalk parameter leafIndex chain 0 step.val value : OracleComp HashSpec Digest)
    beforeCache middleCache cache previous hprevious (hmiddleLe.trans hafter)
  rw [Concrete.CacheReplay.eval_chainWalk] at hwalk
  refine ⟨output, ?_⟩
  rw [hwalk]
  have hposition : (⟨0 + step.val, hstep⟩ : ChainStep) = step := Fin.ext (by simp)
  rw [hposition] at hcached
  exact hafter hcached

/-- The honest top signature of a precomputed key is its replay from the key-generation cache. -/
theorem Concrete.precomputed_topPart_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec)
    (key : TopIndex) :
    Concrete.topPart (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache) key =
      Concrete.CacheReplay.topPartFromCache cache
        (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache) key := by
  unfold Concrete.topPart Concrete.CacheReplay.topPartFromCache
  rcases (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache).topSigned key with
    _ | ⟨randomness, encoding⟩
  · rfl
  · dsimp only
    congr 1
    · funext chain
      simp [Concrete.precomputedSecretKey, Concrete.honestTopValues, Wots.signChain]
    · funext level
      simp [Concrete.precomputedSecretKey, Concrete.honestTopPath, level.isLt]

theorem Concrete.precomputedKeygen_support_consistent
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    PrecomputedKeyConsistent keyResult.2 keyResult.1.2 := by
  obtain ⟨parameter, secret, topSecret, topSigned, hsecretKey⟩ :=
    Concrete.precomputedKeygen_support_secretKey_components keyResult hmem
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  have hstable := keygen_support_treeCacheStable _ hold
  have htopStable := keygen_support_topCacheStable _ hold
  intro largerCache hle leafIndex randomness encoding
  have hchains (chain : ChainIndex) :=
    (Concrete.keygen_runsBelow_chainWalk _ hold leafIndex chain (encoding chain).val
      (Nat.le_pred_of_lt (encoding chain).isLt)).eval_eq largerCache hle
  rw [hsecretKey] at hstable htopStable hchains ⊢
  unfold Concrete.precomputedSignWithEncoding Concrete.CacheReplay.signWithEncoding
  congr 1
  · rw [Concrete.CacheReplay.precomputedSignedChainValues_eq]
    funext chain
    have hchain := hchains chain
    rw [Concrete.CacheReplay.eval_chainWalk, Concrete.CacheReplay.eval_chainWalk] at hchain
    exact hchain
  · rw [Concrete.CacheReplay.precomputedAuthenticationPath_eq]
    exact CappedChain.TreeCacheStable.authenticationPath_eq
      (Concrete.precomputedSecretKey parameter secret topSecret topSigned keyResult.2) keyResult.2
      hstable largerCache hle leafIndex
  · rw [Concrete.precomputed_topPart_eq]
    exact htopStable largerCache hle (topKeyOf leafIndex)
theorem Concrete.precomputedKeygen_cache_none_encodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (targetLeafIndex : LeafIndex) (targetInput : Message × Randomness) :
    keyResult.2
      (Concrete.CacheView.encodingInput keyResult.1.2.parameter targetLeafIndex targetInput) =
        none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Concrete.keygen_cache_none_encodingInput oldKeyResult hold targetLeafIndex targetInput

theorem Concrete.precomputedKeygen_chainWalk_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) :
    Wots.walk
        (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
        0 steps (keyResult.1.2.chainStart leafIndex chain) =
      Wots.walk
        (Concrete.CacheView.chainStep largerCache keyResult.1.2.parameter leafIndex chain)
        0 steps (keyResult.1.2.chainStart leafIndex chain) := by
  have heval := (Concrete.keygen_runsBelow_chainWalk _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) leafIndex chain steps
    hsteps).eval_eq largerCache hle
  rw [Concrete.CacheReplay.eval_chainWalk, Concrete.CacheReplay.eval_chainWalk] at heval
  exact heval
theorem Concrete.precomputedKeygen_cache_has_chainInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex chain step
        (Wots.walk
          (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
          0 step.val (keyResult.1.2.chainStart leafIndex chain))) = some output :=
  (Concrete.keygen_runsBelow_chainWalk _ (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem)
    leafIndex chain (step.val + 1) step.isLt).chainInput_cached step
theorem Concrete.precomputedKeygen_cache_chainInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (hne : value ≠ Wots.walk
      (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
      0 step.val (keyResult.1.2.chainStart leafIndex chain)) :
    keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex chain step value) = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.precomputedKeygen_cache_has_chainInput keyResult hmem leafIndex chain step
  cases hcandidate : keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex chain step value) with
  | none => rfl
  | some candidateOutput =>
      exfalso
      apply hne
      apply Concrete.CacheView.chainInput_injective keyResult.1.2.parameter leafIndex chain step
      exact Concrete.keygen_cache_unique_chainAddress _
        (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) leafIndex chain step _ _
        candidateOutput honestOutput
        ((atHashAddress_tweakableHashInput_iff keyResult.1.2.parameter _ _ _).2 rfl)
        ((atHashAddress_tweakableHashInput_iff keyResult.1.2.parameter _ _ _).2 rfl) hcandidate hhonest
theorem Concrete.precomputedKeygen_cache_has_chainValue_preimage
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit)
    (hpositive : 0 < digit.val) :
    ∃ previous : ChainStep, ∃ output,
      previous.val + 1 = digit.val ∧
      keyResult.2
        (Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex chain previous
          (Wots.walk
            (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
            0 previous.val (keyResult.1.2.chainStart leafIndex chain))) = some output ∧
      truncateHash output =
        Wots.signChain
          (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
          digit (keyResult.1.2.chainStart leafIndex chain) := by
  let previous : ChainStep := ⟨digit.val - 1, by
    have hdigit := digit.isLt
    omega⟩
  obtain ⟨output, hcached⟩ :=
    Concrete.precomputedKeygen_cache_has_chainInput keyResult hmem leafIndex chain previous
  refine ⟨previous, output, by dsimp only [previous]; omega, hcached, ?_⟩
  let step := Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain
  calc
    truncateHash output = Concrete.CacheView.digestAt keyResult.2
        (Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex chain previous
          (Wots.walk step 0 previous.val
            (keyResult.1.2.chainStart leafIndex chain))) :=
      (Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached).symm
    _ = step previous.val
        (Wots.walk step 0 previous.val (keyResult.1.2.chainStart leafIndex chain)) := by
      symm
      exact Concrete.CacheView.chainStep_eq keyResult.2 keyResult.1.2.parameter leafIndex chain
        previous.val _ previous.isLt
    _ = Wots.signChain step digit (keyResult.1.2.chainStart leafIndex chain) := by
      unfold Wots.signChain
      rw [show digit.val = previous.val + 1 by dsimp only [previous]; omega]
      simp only [Wots.walk, zero_add]
theorem Concrete.precomputedKeygen_cache_has_merkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output :=
  Concrete.keygen_cache_has_merkleInput_in_largerCache _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) largerCache hle level node
    (hnode.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
theorem Concrete.precomputedKeygen_cache_merkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false),
        Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) :
    keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) = none :=
  Concrete.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) largerCache hle level node
    (hnode.trans_le (Nat.pow_le_pow_right (by omega) (by omega))) left right hne
theorem Concrete.precomputedKeygen_merkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) =
    (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) :=
  Concrete.keygen_merkleChildren_eq_of_cache_le _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) largerCache hle level node
    (hnode.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
end XmssSecurity
