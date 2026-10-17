import XmssSecurity.Proof.CappedLeafEventProbability
import XmssSecurity.Proof.CappedSuffixEventProbability
import XmssSecurity.Proof.ChainTargetInput

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

set_option maxRecDepth 100000

theorem keygenChainTargetInput_eq_capped
    (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    keygenChainTargetInput secretKey cache =
      CappedSuffix.keygenChainTargetInput secretKey cache := by
  funext input
  by_cases h : ∃ address : LeafIndex × ChainIndex × ChainStep, ∃ value,
      input = Concrete.CacheView.chainInput secretKey.parameter address.1
        address.2.1 address.2.2 value
  · obtain ⟨address, value, rfl⟩ := h
    rw [XmssSecurity.keygenChainTargetInput_chainInput,
      CappedSuffix.keygenChainTargetInput_chainInput]
  · unfold keygenChainTargetInput CappedSuffix.keygenChainTargetInput
    rfl

noncomputable def OutcomeChainValueRevealed (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
          outcome.forgery.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
      outcome.forgery.signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep cache outcome.secretKey.parameter
            outcome.forgery.leafIndex chain)
          (encoding chain) (outcome.secretKey.chainStart outcome.forgery.leafIndex chain)

noncomputable def OutcomeChainValueHasKeygenOrigin (keygenCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey) (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          outcome.forgery.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
      (((encoding chain).val = 0 ∧
          outcome.forgery.signature.chainValue chain =
            secretKey.chainStart outcome.forgery.leafIndex chain) ∨
        ∃ previous : ChainStep, ∃ output,
          previous.val + 1 = (encoding chain).val ∧
          keygenCache
            (Concrete.CacheView.chainInput secretKey.parameter
              outcome.forgery.leafIndex chain previous
              (Wots.walk
                (Concrete.CacheView.chainStep keygenCache secretKey.parameter
                  outcome.forgery.leafIndex chain)
                0 previous.val
                (secretKey.chainStart outcome.forgery.leafIndex chain))) = some output ∧
          truncateHash output = outcome.forgery.signature.chainValue chain)

theorem chainValueRevealed_afterKeygen_has_origin
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (chain : ChainIndex)
    (hrevealed : OutcomeChainValueRevealed execution.2 execution.1 chain) :
    OutcomeChainValueHasKeygenOrigin keyResult.2 execution.2 keyResult.1.2 execution.1 chain := by
  obtain ⟨hverified, encoding, hdecode, hvalue⟩ := hrevealed
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  rw [hkeys.2] at hdecode hvalue
  have hcacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hwalk := Concrete.precomputedKeygen_chainWalk_eq_of_cache_le keyResult hkeygen'
    execution.2
    hcacheLe execution.1.forgery.leafIndex chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  refine ⟨hverified, encoding, hdecode, ?_⟩
  by_cases hzero : (encoding chain).val = 0
  · left
    refine ⟨hzero, ?_⟩
    simpa [Wots.signChain, hzero] using hvalue
  · right
    have hpositive : 0 < (encoding chain).val := Nat.pos_of_ne_zero hzero
    obtain ⟨previous, output, hprevious, hcached, houtput⟩ :=
      Concrete.precomputedKeygen_cache_has_chainValue_preimage keyResult hkeygen'
        execution.1.forgery.leafIndex chain (encoding chain) hpositive
    refine ⟨previous, output, hprevious, ?_, ?_⟩
    · exact hcached
    · calc
        truncateHash output = Wots.signChain
            (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter
              execution.1.forgery.leafIndex chain)
            (encoding chain)
            (keyResult.1.2.chainStart execution.1.forgery.leafIndex chain) := houtput
        _ = Wots.signChain
            (Concrete.CacheView.chainStep execution.2 keyResult.1.2.parameter
              execution.1.forgery.leafIndex chain)
            (encoding chain)
            (keyResult.1.2.chainStart execution.1.forgery.leafIndex chain) := hwalk
        _ = execution.1.forgery.signature.chainValue chain := hvalue.symm

theorem chain_event_afterKeygen_revealed_or_collision
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (chain : ChainIndex)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.chain chain)) :
    OutcomeChainValueRevealed execution.2 execution.1 chain ∨
      Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
        (keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hchain⟩ := hsame
    have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
      execution hafter
    have hsignature := CappedLeaf.detailed_execution_returned_signature_eq adversary execution hgame
      request signature signedEncoding hsignedDecode hreturned
    change Wots.IsBackwardWitnessAt
      (fun candidateChain => Concrete.CacheView.chainStep execution.2
        execution.1.secretKey.parameter request.leafIndex candidateChain)
      signedEncoding forgedEncoding signature.chainValue
      execution.1.forgery.signature.chainValue chain at hchain
    have hsignedValue : signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            request.leafIndex chain)
          (signedEncoding chain) (execution.1.secretKey.chainStart request.leafIndex chain) := by
      rw [hsignature]
      rfl
    rcases Wots.backwardWitness_eq_honest_or_hasStepCollision
      (fun candidateChain => Concrete.CacheView.chainStep execution.2
        execution.1.secretKey.parameter request.leafIndex candidateChain)
      signedEncoding forgedEncoding signature.chainValue
      execution.1.forgery.signature.chainValue
      (execution.1.secretKey.chainStart request.leafIndex) chain hsignedValue hchain with
      hrevealed | hcollision
    · left
      refine ⟨hevent.1, forgedEncoding, ?_, ?_⟩
      · simpa [hleafIndex] using hforgedDecode
      · simpa [hleafIndex] using hrevealed
    · right
      obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
      have hposition : offset < chainLength - 1 - (forgedEncoding chain).val := by
        have hsignedLt := (signedEncoding chain).isLt
        have hforgedLe := hchain.1.le
        omega
      let position : TargetSum.SuffixPosition forgedEncoding :=
        ⟨chain, ⟨offset, hposition⟩⟩
      have hsuffix : Wots.IsSuffixCollisionAt
          (fun candidateChain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.leafIndex candidateChain)
          forgedEncoding forgedEncoding
          (fun candidateChain => Wots.signChain
            (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
              execution.1.forgery.leafIndex candidateChain)
            (forgedEncoding candidateChain)
            (execution.1.secretKey.chainStart execution.1.forgery.leafIndex candidateChain))
          execution.1.forgery.signature.chainValue position := by
        dsimp only [Wots.IsSuffixCollisionAt, position]
        simp only [Nat.sub_self, Wots.walk_zero]
        exact ⟨le_rfl, by simpa only [hleafIndex] using hne,
          by simpa only [hleafIndex] using heq⟩
      have hforgedDecode' : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex
            (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some forgedEncoding := by
        simpa [hleafIndex] using hforgedDecode
      rw [keygenChainTargetInput_eq_capped]
      exact CappedSuffix.fresh_suffix_witness_afterKeygen_orientation adversary keyResult hkeygen execution
        hafter forgedEncoding hevent.1 hforgedDecode' position hsuffix
  · left
    obtain ⟨forgedEncoding, _hforgedValid, _hunsigned, hforgedDecode, hchain⟩ := hfresh
    refine ⟨hevent.1, forgedEncoding, hforgedDecode, ?_⟩
    exact hchain

end XmssSecurity.CappedChain
