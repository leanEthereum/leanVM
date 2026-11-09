module

public import XmssSecurity.Proof.CappedChain.ChainRevealFiltering

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def ChainValueIndicesForwardClosed
    (covered : Set ChainValueIndex) : Prop :=
  ∀ key earlier later,
    (key, earlier) ∈ covered → earlier ≤ later →
      (key, later) ∈ covered

noncomputable def ReturnedChainValueCovered
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    Set ChainValueIndex :=
  fun index => index ∈ returnedChainValueIndexList cache secretKey log chain

theorem returnedChainValueCovered_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ ReturnedChainValueCovered cache secretKey log chain ↔
      ReturnedChainValueIndex cache secretKey log chain index := by
  exact mem_returnedChainValueIndexList_iff cache secretKey log chain index

theorem returnedChainValueCovered_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    ChainValueIndicesForwardClosed
      (ReturnedChainValueCovered cache secretKey log chain) := by
  intro key earlier later hmem hle
  rw [returnedChainValueCovered_iff] at hmem ⊢
  rcases hmem with ⟨request, signature, encoding, hreturned, hdecode, hkey, hdigit⟩ |
    ⟨request, signature, randomness, topEncoding, hreturned, htop, hkey, hdigit⟩
  · exact Or.inl ⟨request, signature, encoding, hreturned, hdecode, hkey, hdigit.trans hle⟩
  · exact Or.inr ⟨request, signature, randomness, topEncoding, hreturned, htop, hkey,
      hdigit.trans hle⟩

theorem returnedChainValueCovered_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache secretKey.parameter request.leafIndex
        (request.message, signature.randomness)) = some encoding) :
    (.inl request.leafIndex, encoding chain) ∈
      ReturnedChainValueCovered cache secretKey log chain := by
  rw [returnedChainValueCovered_iff]
  exact Or.inl ⟨request, signature, encoding, hreturned, hdecode, rfl, le_rfl⟩

theorem returnedChainValueCovered_contains_returnedTop
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (request : SignRequest) (signature : Signature)
    (randomness : Randomness) (topEncoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (htop : secretKey.topSigned (topKeyOf request.leafIndex) = some (randomness, topEncoding)) :
    (.inr (topKeyOf request.leafIndex), topEncoding chain) ∈
      ReturnedChainValueCovered cache secretKey log chain := by
  rw [returnedChainValueCovered_iff]
  exact Or.inr ⟨request, signature, randomness, topEncoding, hreturned, htop, rfl, le_rfl⟩

theorem returnedChainValueCovered_iff_mem_indices
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ ReturnedChainValueCovered cache secretKey log chain ↔
      index ∈ returnedChainValueIndices cache secretKey log chain := by
  rw [returnedChainValueCovered_iff, mem_returnedChainValueIndices_iff]

end XmssSecurity.CappedChain
