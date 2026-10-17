import XmssSecurity.Proof.ChainInputTrace
import XmssSecurity.Proof.HashInputLemmas
import XmssSecurity.Proof.WinningEventReduction
import XmssSecurity.Proof.ChainKey

open OracleSpec

namespace XmssSecurity

abbrev ChainValueIndex := ChainKey × Digit

def chainStepDigit (step : ChainStep) : Digit :=
  ⟨step.val, step.isLt.trans (by decide)⟩

theorem Concrete.CacheView.chainInput_eq_iff
    (parameter : PublicParameter)
    (leftLeafIndex rightLeafIndex : LeafIndex) (leftChain rightChain : ChainIndex)
    (leftStep rightStep : ChainStep) (leftValue rightValue : Digest) :
    Concrete.CacheView.chainInput parameter leftLeafIndex leftChain leftStep leftValue =
        Concrete.CacheView.chainInput parameter rightLeafIndex rightChain rightStep rightValue ↔
      leftLeafIndex = rightLeafIndex ∧ leftChain = rightChain ∧
        leftStep = rightStep ∧ leftValue = rightValue := by
  constructor
  · intro heq
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    simp only [HashDomain.chain.injEq] at hdomain
    obtain ⟨hleafIndex, hchain, hstep⟩ := hdomain
    subst rightLeafIndex
    subst rightChain
    subst rightStep
    refine ⟨rfl, rfl, rfl, ?_⟩
    exact Concrete.CacheView.chainInput_injective parameter leftLeafIndex leftChain
      leftStep heq
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

noncomputable def keygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : ChainValueIndex → Digest := fun index =>
  Wots.walk
    (Concrete.CacheView.keyChainStep keygenCache secretKey.parameter index.1 chain)
    0 index.2.val (secretKey.keyChainStart index.1 chain)

/-- The chain coordinate used by a winning chain event precedes the coordinate returned by every successful signature at the forged leaf index. -/
theorem WinningOutcomeBadEventOccurs.chain_coordinate_lt_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding)
    (request : SignRequest) (signature : Signature) (signedEncoding : Encoding)
    (hreturned : SigningTranscript.Returned outcome.signingLog request signature)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.leafIndex
        (request.message, signature.randomness)) = some signedEncoding)
    (hleafIndex : request.leafIndex = outcome.forgery.leafIndex) :
    forgedEncoding chain < signedEncoding chain := by
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨eventRequest, eventSignature, eventSignedEncoding, eventForgedEncoding,
      heventSignedDecode, heventForgedDecode, heventReturned, heventLeafIndex,
      hchain⟩ := hsame
    have hreturnedEq := SigningTranscript.returned_eq_of_same_leafIndex
      hevent.signingTranscript_valid heventReturned hreturned
      (heventLeafIndex.trans hleafIndex.symm)
    obtain ⟨hrequest, hsignature⟩ := hreturnedEq
    subst request
    subst signature
    have hsignedEncoding : eventSignedEncoding = signedEncoding := by
      rw [heventSignedDecode] at hsignedDecode
      exact Option.some.inj hsignedDecode
    have hforgedEncoding : eventForgedEncoding = forgedEncoding := by
      rw [heventLeafIndex] at heventForgedDecode
      rw [heventForgedDecode] at hforgedDecode
      exact Option.some.inj hforgedDecode
    change Wots.IsBackwardWitnessAt
      (fun candidateChain => Concrete.CacheView.chainStep cache
        outcome.secretKey.parameter eventRequest.leafIndex candidateChain)
      eventSignedEncoding eventForgedEncoding eventSignature.chainValue
      outcome.forgery.signature.chainValue chain at hchain
    rw [← hsignedEncoding, ← hforgedEncoding]
    exact hchain.1
  · obtain ⟨_eventForgedEncoding, _hvalid, hunsigned, _hdecode, _hchain⟩ := hfresh
    exact (hunsigned ⟨request, signature, hreturned, hleafIndex⟩).elim

/-- The coordinates a returned signature sends at a chain of either layer: the bottom one at its
leaf index and the top one of its bottom tree. -/
def ReturnedChainValueIndex
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) (index : ChainValueIndex) : Prop :=
  (∃ request signature encoding,
    SigningTranscript.Returned log request signature ∧
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding ∧
      index.1 = .inl request.leafIndex ∧ encoding chain ≤ index.2) ∨
  (∃ request signature randomness topEncoding,
    SigningTranscript.Returned log request signature ∧
      secretKey.topSigned (topKeyOf request.leafIndex) = some (randomness, topEncoding) ∧
      index.1 = .inr (topKeyOf request.leafIndex) ∧ topEncoding chain ≤ index.2)

/-- Coordinates sent by the signer, together with every later coordinate that can be derived by walking the chain forward. -/
noncomputable def returnedChainValueIndices
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) : Finset ChainValueIndex := by
  classical
  exact Finset.univ.filter (ReturnedChainValueIndex cache secretKey log chain)

@[simp]
theorem mem_returnedChainValueIndices_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) (index : ChainValueIndex) :
    index ∈ returnedChainValueIndices cache secretKey log chain ↔
      ReturnedChainValueIndex cache secretKey log chain index := by
  classical
  simp only [returnedChainValueIndices, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem WinningOutcomeBadEventOccurs.forged_chain_coordinate_not_mem_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding) :
    (.inl outcome.forgery.leafIndex, forgedEncoding chain) ∉
      returnedChainValueIndices cache outcome.secretKey outcome.signingLog chain := by
  intro hmem
  rw [mem_returnedChainValueIndices_iff] at hmem
  rcases hmem with ⟨request, signature, signedEncoding, hreturned, hsignedDecode,
    hleafIndex, hdigit⟩ | ⟨_, _, _, _, _, _, hkey, _⟩
  swap
  · cases hkey
  have hleafIndex : request.leafIndex = outcome.forgery.leafIndex := by
    exact (Sum.inl_injective hleafIndex).symm
  have hbackward := hevent.chain_coordinate_lt_returned forgedEncoding
    hforgedDecode request signature signedEncoding hreturned hsignedDecode hleafIndex
  exact (not_lt_of_ge hdigit) hbackward

end XmssSecurity
