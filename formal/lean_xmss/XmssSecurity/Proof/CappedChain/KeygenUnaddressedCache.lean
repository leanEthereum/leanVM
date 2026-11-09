module

public import XmssSecurity.Proof.KeygenCache
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def KeygenAddressedHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ domain, AtHashAddress parameter domain input

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (KeygenAddressedHashInput parameter) :=
  Classical.decPred _

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
