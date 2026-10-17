import XmssSecurity.Proof.MerkleQueryBound
import XmssSecurity.Proof.Execution
import XmssSecurity.Proof.LazyScheme

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.keygen_support_rootTree
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    ∃ (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
      (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
      (result : Digest × (TopIndex → Option (Randomness × Encoding))),
      keyResult.1 = (⟨result.1, parameter⟩,
        SecretKey.withoutPrecomputation parameter secret topSecret result.2) ∧
      (result, keyResult.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
            OracleComp HashSpec _)).run ∅) := by
  unfold Concrete.keygen at hmem
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
  cases hout
  have h1 : parameterCache = ∅ :=
    xmssRom_lift_probComp_cache_eq Concrete.samplePublicParameter ∅ (parameter, parameterCache) hparameter
  have h2 : secretCache = parameterCache :=
    xmssRom_lift_probComp_cache_eq Concrete.sampleSecret parameterCache (secret, secretCache) hsecret
  have h3 : topSecretCache = secretCache :=
    xmssRom_lift_probComp_cache_eq Concrete.sampleTopSecret secretCache (topSecret, topSecretCache) htopSecret
  have h4 : topBaseCache = topSecretCache :=
    xmssRom_lift_probComp_cache_eq Concrete.sampleTopBase topSecretCache (topBase, topBaseCache) htopBase
  let honest : OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
    Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key))
  have hroute :
      simulateQ romImpl (liftM honest) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) honest := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) honest
  rw [hroute, h4, h3, h2, h1] at hresult
  exact ⟨parameter, secret, topSecret, topBase, result, rfl, hresult⟩

/-- Key generation's honest computation queries no bottom encoding input. -/
theorem Concrete.honestKeygen_queryBound_zero_encodingAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLeafIndex : LeafIndex) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.encoding targetLeafIndex)) 0 :=
  Concrete.honestKeygen_queryBound_zero parameter _ secret topSecret _
    (rejectsTop_atHashAddress parameter _ rfl)
    (fun domain payload _ hne hat => hne targetLeafIndex
      ((atHashAddress_tweakableHashInput_iff parameter _ domain payload).1 hat))
    fun _ _ => by simp

theorem Concrete.keygen_cache_unique_leafAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetLeafIndex : LeafIndex) (left right : HashInput)
    (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter (.leaf targetLeafIndex) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter (.leaf targetLeafIndex) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact Concrete.CacheReplay.rootTree_cache_unique_leafAddress parameter secret topSecret topBase root
    keyResult.2 hroot targetLeafIndex left right leftOutput rightOutput
    hleftP hrightP hleft hright

theorem Concrete.keygen_cache_unique_chainAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter
      (.chain targetLeafIndex targetChain targetStep) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter
      (.chain targetLeafIndex targetChain targetStep) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact Concrete.CacheReplay.rootTree_cache_unique_chainAddress parameter secret topSecret topBase root
    keyResult.2 hroot targetLeafIndex targetChain targetStep left right leftOutput rightOutput
    hleftP hrightP hleft hright

theorem Concrete.keygen_cache_unique_merkleAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress keyResult.1.2.parameter
      (.merkle targetLevel targetNode) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter
      (.merkle targetLevel targetNode) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact Concrete.CacheReplay.rootTree_cache_unique_merkleAddress parameter secret topSecret topBase root
    keyResult.2 hroot targetLevel targetNode left right leftOutput rightOutput
    hleftP hrightP hleft hright

/-- Key generation evaluates only chain, leaf, and Merkle domains, so its cache contains no encoding input. -/
theorem Concrete.keygen_cache_none_encodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (targetLeafIndex : LeafIndex) (targetInput : Message × Randomness) :
    keyResult.2
      (Concrete.CacheView.encodingInput keyResult.1.2.parameter targetLeafIndex targetInput) =
        none := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (Concrete.CacheView.encodingInput parameter targetLeafIndex targetInput)
    ∅ keyResult.2 root
  · exact (Concrete.honestKeygen_queryBound_zero_encodingAddress parameter secret topSecret topBase
      targetLeafIndex).of_imp (by
        intro input hinput
        subst input
        rw [Concrete.CacheView.encodingInput]
        exact atHashAddress_tweakableHashInput_iff parameter
          (.encoding targetLeafIndex) (.encoding targetLeafIndex) _ |>.2 rfl)
  · simp
  · exact hroot

end XmssSecurity
