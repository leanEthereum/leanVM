import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.ChainKey
import XmssSecurity.Proof.TopKeygenQueryBound
import XmssSecurity.Proof.HonestKeygenRun
import XmssSecurity.Proof.QueryPresence

/-!
# Key generation's top layer

Top counterparts of the bottom facts of `TreeQueryBound` and `KeygenCache`: key generation queries
each top chain-step address at most once.
-/

open OracleComp OracleSpec

namespace XmssSecurity

attribute [local irreducible] Concrete.topTreeNode

/-- A supported execution of key generation's honest computation from an empty cache contains at
most one input at each top chain-step address. -/
theorem Concrete.CacheReplay.honestKeygen_cache_unique_topChainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetKey : TopIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.topChain targetKey targetChain targetStep) left)
    (hrightP : AtHashAddress parameter (.topChain targetKey targetChain targetStep) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right :=
  Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.topChain targetKey targetChain targetStep)) ∅ cache result
    (Concrete.honestKeygen_queryBound_topChainAddress parameter secret topSecret topBase targetKey
      targetChain targetStep)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

theorem Concrete.keygen_cache_unique_keyChainAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (key : ChainKey) (chain : ChainIndex) (step : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter (key.chainDomain chain step) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter (key.chainDomain chain step) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  cases key with
  | inl leafIndex =>
      exact Concrete.keygen_cache_unique_chainAddress keyResult hmem leafIndex chain step
        left right leftOutput rightOutput hleftP hrightP hleft hright
  | inr key =>
      obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
        Concrete.keygen_support_rootTree keyResult hmem
      rw [hkey] at hleftP hrightP
      exact Concrete.CacheReplay.honestKeygen_cache_unique_topChainAddress parameter secret
        topSecret topBase root keyResult.2 hroot key chain step left right leftOutput rightOutput
        hleftP hrightP hleft hright

/-- A supported execution of key generation's honest computation from an empty cache contains at
most one input at each top leaf address. -/
theorem Concrete.CacheReplay.honestKeygen_cache_unique_topLeafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetKey : TopIndex) (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.topLeaf targetKey) left)
    (hrightP : AtHashAddress parameter (.topLeaf targetKey) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right :=
  Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.topLeaf targetKey)) ∅ cache result
    (Concrete.honestKeygen_queryBound_topLeafAddress parameter secret topSecret topBase targetKey)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

/-- Key generation's cache holds the honest leaf of every one-time key of both layers. -/
theorem Concrete.keygen_cache_has_keyLeafInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (key : ChainKey) :
    ∃ output,
      keyResult.2 (Concrete.CacheView.keyLeafInput keyResult.1.2.parameter key
        (Concrete.CacheReplay.keyOneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.keyChainStart key)) = some output := by
  cases key with
  | inl leafIndex => exact Concrete.keygen_cache_has_leafInput keyResult hmem leafIndex
  | inr key =>
      obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
        Concrete.keygen_support_rootTree keyResult hmem
      rw [hkey]
      obtain ⟨beforeCache, afterCache, value, hrun, hafter⟩ :=
        Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hroot 0 key (by omega)
          (by rw [Nat.sub_zero]; exact key.isLt)
      rw [Concrete.topTreeNode, Concrete.topLeafAt] at hrun
      obtain ⟨endpoints, middleCache, hendpoints, hleaf, hmiddleLe⟩ :=
        Concrete.CacheReplay.runsBelow_bind_left hrun
      obtain ⟨output, hcached, _⟩ := Concrete.CacheReplay.tweakableHash_query_cached parameter
        (.topLeaf key) (Concrete.leafPayload endpoints) middleCache afterCache value hleaf
      have hreplay := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.topOneTimePublicKey parameter topSecret key :
          OracleComp HashSpec (ChainIndex → Digest))
        beforeCache middleCache keyResult.2 endpoints hendpoints (hmiddleLe.trans hafter)
      have hendpointsEq : endpoints = Concrete.CacheReplay.topOneTimePublicKey keyResult.2
          parameter topSecret key := by
        rw [← hreplay]
        funext chain
        simp [Concrete.topOneTimePublicKey, Concrete.CacheReplay.topOneTimePublicKey]
      refine ⟨output, ?_⟩
      have h := hafter hcached
      rw [hendpointsEq] at h
      exact h

theorem Concrete.keygen_cache_unique_keyLeafAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (key : ChainKey) (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter key.leafDomain left)
    (hrightP : AtHashAddress keyResult.1.2.parameter key.leafDomain right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  cases key with
  | inl leafIndex =>
      exact Concrete.keygen_cache_unique_leafAddress keyResult hmem leafIndex
        left right leftOutput rightOutput hleftP hrightP hleft hright
  | inr key =>
      obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
        Concrete.keygen_support_rootTree keyResult hmem
      rw [hkey] at hleftP hrightP
      exact Concrete.CacheReplay.honestKeygen_cache_unique_topLeafAddress parameter secret
        topSecret topBase root keyResult.2 hroot key left right leftOutput rightOutput
        hleftP hrightP hleft hright

/-- A distinct leaf payload at a one-time key's leaf address is absent after key generation. -/
theorem Concrete.keygen_cache_keyLeafInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (key : ChainKey) (endpoints : ChainIndex → Digest)
    (hne : endpoints ≠ Concrete.CacheReplay.keyOneTimePublicKey keyResult.2
      keyResult.1.2.parameter keyResult.1.2.keyChainStart key) :
    keyResult.2 (Concrete.CacheView.keyLeafInput keyResult.1.2.parameter key endpoints) =
      none := by
  cases key with
  | inl leafIndex =>
      exact Concrete.keygen_cache_leafInput_eq_none_of_ne keyResult hmem leafIndex endpoints hne
  | inr key =>
      obtain ⟨honestOutput, hhonest⟩ := Concrete.keygen_cache_has_keyLeafInput keyResult hmem
        (.inr key)
      cases hforged : keyResult.2
          (Concrete.CacheView.keyLeafInput keyResult.1.2.parameter (.inr key) endpoints) with
      | none => rfl
      | some forgedOutput =>
          exfalso
          apply hne
          obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
            Concrete.keygen_support_rootTree keyResult hmem
          have hparameter : keyResult.1.2.parameter = parameter := by rw [hkey]; rfl
          have heq := Concrete.CacheReplay.honestKeygen_cache_unique_topLeafAddress parameter
            secret topSecret topBase root keyResult.2 hroot key _ _ forgedOutput honestOutput
            (by rw [← hparameter]; exact (atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)
            (by rw [← hparameter]; exact (atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)
            hforged hhonest
          exact ((Concrete.CacheView.keyLeafInput_eq_iff _ _ _ _ _).mp heq).2

end XmssSecurity
