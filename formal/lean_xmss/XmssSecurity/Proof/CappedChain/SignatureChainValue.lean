import XmssSecurity.Proof.PrecomputedKeygenCache
import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.CappedChain.ChainHiddenTable

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def replaceSignatureChainValue
    (signature : Signature) (chain : ChainIndex) (value : Digest) : Signature :=
  { signature with
    chainValue := Function.update signature.chainValue chain value }

@[simp]
theorem replaceSignatureChainValue_same
    (signature : Signature) (chain : ChainIndex) (value : Digest) :
    (replaceSignatureChainValue signature chain value).chainValue chain = value := by
  simp [replaceSignatureChainValue]

theorem replaceSignatureChainValue_other
    (signature : Signature) (chain candidate : ChainIndex) (value : Digest)
    (hne : candidate ≠ chain) :
    (replaceSignatureChainValue signature chain value).chainValue candidate =
      signature.chainValue candidate := by
  simp [replaceSignatureChainValue, Function.update_of_ne hne]

theorem Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding)
    (chain : ChainIndex) :
    (Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
      leafIndex randomness encoding).chainValue chain =
      keygenChainValueTable keyResult.2 keyResult.1.2 chain
        (.inl leafIndex, encoding chain) := by
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen
    largerCache hle (.inl leafIndex) chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  simp only [Concrete.CacheReplay.signWithEncoding,
    Concrete.CacheReplay.signedChainValues, keygenChainValueTable]
  exact hwalk.symm

/-- Replace one top chain value of a signature. -/
def replaceSignatureTopChainValue
    (signature : Signature) (chain : ChainIndex) (value : Digest) : Signature :=
  { signature with
    top := { signature.top with
      chainValue := Function.update signature.top.chainValue chain value } }

@[simp]
theorem replaceSignatureTopChainValue_same
    (signature : Signature) (chain : ChainIndex) (value : Digest) :
    (replaceSignatureTopChainValue signature chain value).top.chainValue chain = value := by
  simp [replaceSignatureTopChainValue]

theorem replaceSignatureTopChainValue_other
    (signature : Signature) (chain candidate : ChainIndex) (value : Digest)
    (hne : candidate ≠ chain) :
    (replaceSignatureTopChainValue signature chain value).top.chainValue candidate =
      signature.top.chainValue candidate := by
  simp [replaceSignatureTopChainValue, Function.update_of_ne hne]

theorem Concrete.CacheReplay.topPartFromCache_chainValue_eq_keygenChainValueTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : keyResult.1.2.topSigned key = some (randomness, encoding))
    (chain : ChainIndex) :
    (Concrete.CacheReplay.topPartFromCache largerCache keyResult.1.2 key).chainValue chain =
      keygenChainValueTable keyResult.2 keyResult.1.2 chain
        (.inr key, encoding chain) := by
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen
    largerCache hle (.inr key) chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  simp only [Concrete.CacheReplay.topPartFromCache, hsigned, Concrete.honestTopValues,
    keygenChainValueTable, Wots.signChain]
  exact hwalk.symm

end XmssSecurity.CappedChain
