import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def KeygenAddressedHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ domain, AtHashAddress parameter domain input

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (KeygenAddressedHashInput parameter) :=
  Classical.decPred _

theorem Concrete.tweakableHash_queryBound_zero_unaddressed
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  simp only [Concrete.tweakableHash, Concrete.oracleHash, HasQuery.instOfMonadLift_query,
    bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro hunaddressed
  exact absurd ⟨domain, by simp⟩ hunaddressed

theorem Concrete.chainWalk_queryBound_zero_unaddressed
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Concrete.oneTimePublicKey_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Concrete.oneTimePublicKey]
  apply Concrete.sequenceFin_queryBound_zero
  intro chain
  exact Concrete.chainWalk_queryBound_zero_unaddressed parameter leafIndex chain
    0 (chainLength - 1) (secret leafIndex chain)

theorem Concrete.leafAt_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    (Concrete.leafAt parameter secret leafIndex :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Concrete.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.oneTimePublicKey_queryBound_zero_unaddressed parameter secret
      leafIndex) ?_
  intro endpoints _
  exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _

theorem Concrete.treeNode_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact Concrete.leafAt_queryBound_zero_unaddressed parameter secret node
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Concrete.childNode node false)) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Concrete.childNode node true)) ?_
      intro right _
      split
      · exact Concrete.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Concrete.honestKeygen_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 :=
  have haddressed (domain : HashDomain) (payload : HashInput) :
      ¬ ¬ KeygenAddressedHashInput parameter (tweakableHashInput parameter domain payload) :=
    fun h => h ⟨domain, (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl⟩
  Concrete.honestKeygen_queryBound_zero parameter _ secret topSecret _
    (fun domain payload _ => haddressed domain payload)
    (fun domain payload _ _ => haddressed domain payload) fun _ _ => by simp

theorem Concrete.keygen_cache_none_unaddressed
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput)
    (hinput : ¬ KeygenAddressedHashInput keyResult.1.2.parameter input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _) input ∅ keyResult.2 root
  · apply (Concrete.honestKeygen_queryBound_zero_unaddressed parameter secret topSecret topBase).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

theorem Concrete.keygen_cache_none_at_encodingAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (leafIndex : LeafIndex) (input : HashInput)
    (hinput : AtHashAddress keyResult.1.2.parameter (.encoding leafIndex) input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _) input ∅ keyResult.2 root
  · apply (Concrete.honestKeygen_queryBound_zero_encodingAddress parameter secret topSecret topBase
      leafIndex).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

end XmssSecurity.CappedChain
