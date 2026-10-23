import XmssSecurity.Proof.CappedGlobalCollisionProbability
import XmssSecurity.Proof.CappedLeafEventProbability
import XmssSecurity.Proof.GlobalWinningChainValueRevealed
import XmssSecurity.Proof.TopStructural

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxHeartbeats 10000

noncomputable def keygenStructuralTargetInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : HashInput :=
  CappedTop.keygenTopTargetInput secretKey cache
    (CappedMerkle.keygenMerkleTargetInput secretKey cache
      (CappedLeaf.keygenLeafTargetInput secretKey cache
        (CappedSuffix.keygenChainTargetInput secretKey cache input)))

theorem CappedSuffix.keygenChainTargetInput_leafInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
    Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedSuffix.keygenChainTargetInput_merkleInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
    Concrete.CacheView.merkleInput secretKey.parameter level node left right := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_chainInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
    Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_merkleInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
    Concrete.CacheView.merkleInput secretKey.parameter level node left right := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_chainInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
    Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_leafInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
    Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

@[simp]
theorem keygenStructuralTargetInput_chainInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_chainInput,
    CappedLeaf.keygenLeafTargetInput_chainInput_eq_self,
    CappedMerkle.keygenMerkleTargetInput_chainInput_eq_self,
    CappedTop.keygenTopTargetInput_chainInput]
@[simp]
theorem keygenStructuralTargetInput_leafInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_leafInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_leafInput,
    CappedMerkle.keygenMerkleTargetInput_leafInput_eq_self,
    CappedTop.keygenTopTargetInput_leafInput]
@[simp]
theorem keygenStructuralTargetInput_merkleInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_merkleInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_merkleInput_eq_self,
    CappedMerkle.keygenMerkleTargetInput_merkleInput, CappedTop.keygenTopTargetInput_merkleInput]

theorem chainInput_exists_of_keygenChainTargetInput_ne
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hne : CappedSuffix.keygenChainTargetInput secretKey cache input ≠ input) :
    ∃ address : LeafIndex × ChainIndex × ChainStep, ∃ value,
      input = Concrete.CacheView.chainInput secretKey.parameter address.1
        address.2.1 address.2.2 value := by
  unfold CappedSuffix.keygenChainTargetInput at hne
  split at hne
  · assumption
  · exact (hne rfl).elim

theorem leafInput_exists_of_keygenLeafTargetInput_ne
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hne : CappedLeaf.keygenLeafTargetInput secretKey cache input ≠ input) :
    ∃ leafIndex endpoints,
      input = Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints := by
  unfold CappedLeaf.keygenLeafTargetInput at hne
  split at hne
  · assumption
  · exact (hne rfl).elim

theorem merkleInput_exists_of_keygenMerkleTargetInput_ne
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hne : CappedMerkle.keygenMerkleTargetInput secretKey cache input ≠ input) :
    ∃ address : MerkleLevel × MerkleNode, ∃ left right,
      input = Concrete.CacheView.merkleInput secretKey.parameter address.1
        address.2 left right := by
  unfold CappedMerkle.keygenMerkleTargetInput at hne
  split at hne
  · assumption
  · exact (hne rfl).elim

theorem adaptiveFreshDigestCollisionWith_of_target_eq
    (initialCache finalCache : QueryCache HashSpec)
    (sourceTarget target : HashInput → HashInput)
    (heq : ∀ input, sourceTarget input ≠ input →
      target input = sourceTarget input)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      sourceTarget) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache target := by
  obtain ⟨input, output, targetOutput, hfinal, hfresh, htarget, hdigest⟩ :=
    hcollision
  have hne : sourceTarget input ≠ input := by
    intro hsame
    rw [hsame, hfresh] at htarget
    contradiction
  refine ⟨input, output, targetOutput, hfinal, hfresh, ?_, ?_⟩
  · rw [heq input hne]
    exact htarget
  · rw [heq input hne]
    exact hdigest

theorem adaptiveFreshChainCollision_implies_structural
    (initialCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (CappedSuffix.keygenChainTargetInput secretKey initialCache)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenStructuralTargetInput secretKey initialCache) := by
  apply adaptiveFreshDigestCollisionWith_of_target_eq initialCache finalCache
    (CappedSuffix.keygenChainTargetInput secretKey initialCache)
    (keygenStructuralTargetInput secretKey initialCache) _ hcollision
  intro input hne
  obtain ⟨address, value, rfl⟩ :=
    chainInput_exists_of_keygenChainTargetInput_ne secretKey initialCache
      input hne
  exact keygenStructuralTargetInput_chainInput secretKey initialCache
    address.1 address.2.1 address.2.2 value

theorem adaptiveFreshLeafCollision_implies_structural
    (initialCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (CappedLeaf.keygenLeafTargetInput secretKey initialCache)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenStructuralTargetInput secretKey initialCache) := by
  apply adaptiveFreshDigestCollisionWith_of_target_eq initialCache finalCache
    (CappedLeaf.keygenLeafTargetInput secretKey initialCache)
    (keygenStructuralTargetInput secretKey initialCache) _ hcollision
  intro input hne
  obtain ⟨leafIndex, endpoints, rfl⟩ :=
    leafInput_exists_of_keygenLeafTargetInput_ne secretKey initialCache input hne
  exact keygenStructuralTargetInput_leafInput secretKey initialCache leafIndex endpoints

theorem adaptiveFreshMerkleCollision_implies_structural
    (initialCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (CappedMerkle.keygenMerkleTargetInput secretKey initialCache)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenStructuralTargetInput secretKey initialCache) := by
  apply adaptiveFreshDigestCollisionWith_of_target_eq initialCache finalCache
    (CappedMerkle.keygenMerkleTargetInput secretKey initialCache)
    (keygenStructuralTargetInput secretKey initialCache) _ hcollision
  intro input hne
  obtain ⟨address, left, right, rfl⟩ :=
    merkleInput_exists_of_keygenMerkleTargetInput_ne secretKey initialCache
      input hne
  exact keygenStructuralTargetInput_merkleInput secretKey initialCache
    address.1 address.2 left right

theorem CappedSuffix.keygenChainTargetInput_top (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (domain : HashDomain) (message : HashInput) (hdomain : domain.isTop = true) :
    CappedSuffix.keygenChainTargetInput secretKey cache (tweakableHashInput secretKey.parameter domain message) =
      tweakableHashInput secretKey.parameter domain message := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨_, _, h⟩ := h
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_top (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (domain : HashDomain) (message : HashInput) (hdomain : domain.isTop = true) :
    CappedLeaf.keygenLeafTargetInput secretKey cache (tweakableHashInput secretKey.parameter domain message) =
      tweakableHashInput secretKey.parameter domain message := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨_, _, h⟩ := h
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_top (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (domain : HashDomain) (message : HashInput) (hdomain : domain.isTop = true) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache (tweakableHashInput secretKey.parameter domain message) =
      tweakableHashInput secretKey.parameter domain message := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨_, _, _, h⟩ := h
    cases domain_eq_of_tweakableHashInput_eq _ h; simp [HashDomain.isTop] at hdomain
  · rfl

theorem adaptiveFreshTopCollision_implies_structural
    (initialCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (CappedTop.keygenTopTargetInput secretKey initialCache)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenStructuralTargetInput secretKey initialCache) := by
  apply adaptiveFreshDigestCollisionWith_of_target_eq initialCache finalCache
    (CappedTop.keygenTopTargetInput secretKey initialCache)
    (keygenStructuralTargetInput secretKey initialCache) _ hcollision
  intro input hne
  obtain ⟨domain, message, hdomain, rfl⟩ :=
    CappedTop.top_of_keygenTopTargetInput_ne secretKey initialCache input hne
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_top secretKey initialCache domain message hdomain,
    CappedLeaf.keygenLeafTargetInput_top secretKey initialCache domain message hdomain,
    CappedMerkle.keygenMerkleTargetInput_top secretKey initialCache domain message hdomain]

def WinningStructuralCollisionOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  (WinningGlobalBadEventOccurs cache outcome .chain ∧
      ¬GlobalWinningChainValueRevealed cache outcome) ∨
    WinningGlobalBadEventOccurs cache outcome .suffixCollision ∨
    WinningGlobalBadEventOccurs cache outcome .leaf ∨
    WinningGlobalBadEventOccurs cache outcome .merkle ∨
    (WinningGlobalBadEventOccurs cache outcome .top ∧ ¬WinningTopGuessOccurs cache outcome)

theorem winningStructuralCollision_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hevent : WinningStructuralCollisionOccurs execution.2 execution.1) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent with hchain | hsuffix | hleaf | hmerkle | htop
  · obtain ⟨⟨hwin, chain, hchainEvent⟩, hnotRevealed⟩ := hchain
    rcases CappedChain.chain_event_afterKeygen_revealed_or_collision adversary
        keyResult hkeygen execution hafter chain hchainEvent with
      hrevealed | hcollision
    · exact (hnotRevealed ⟨chain, ⟨hwin, hchainEvent⟩, hrevealed⟩).elim
    · apply adaptiveFreshChainCollision_implies_structural
      simpa only [CappedChain.keygenChainTargetInput_eq_capped] using
        hcollision
  · apply adaptiveFreshChainCollision_implies_structural
    exact globalSuffixCollision_event_afterKeygen_orientation adversary
      keyResult hkeygen execution hafter hsuffix.2
  · apply adaptiveFreshLeafCollision_implies_structural
    exact CappedLeaf.leaf_event_afterKeygen_orientation adversary keyResult
      hkeygen execution hafter hleaf.2
  · apply adaptiveFreshMerkleCollision_implies_structural
    exact globalMerkle_event_afterKeygen_orientation adversary keyResult
      hkeygen execution hafter hmerkle.2
  · apply adaptiveFreshTopCollision_implies_structural
    exact winningTopBadEvent_afterKeygen_orientation adversary keyResult hkeygen execution hafter
      htop.1 htop.2

theorem winningStructuralCollision_probability_le_expectedMovedQueries
    (adversary : Adversary) :
    Pr{let execution ← detailedGameWithCache Concrete.scheme adversary}[WinningStructuralCollisionOccurs execution.2 execution.1] ≤
      (∑' keyResult,
        Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
          expectedSimulatedQueryCount romImpl
            (Rom.IsRelevantHashQuery fun input =>
              keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
            (detailedGameAfterKeygen Concrete.scheme adversary
              keyResult.1.1 keyResult.1.2) keyResult.2) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  apply outcomePredicate_probability_le_expectedMovedQueries_of_afterKeygen_freshCollision
    adversary _ (fun key cache => keygenStructuralTargetInput key.2 cache)
  exact winningStructuralCollision_afterKeygen_orientation adversary

end XmssSecurity
