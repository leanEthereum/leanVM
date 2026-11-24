module

public import XmssSecurity.Proof.ChainOraclePresampling

@[expose] public section

/-!
# Writing and replaying a signature's chain values

`replaceSignatureChainValue` overwrites one chain value of a signature at the layer of a chain key,
as the causal simulation does when it reveals one. Over a cache extending key generation's, the
chain values of `Concrete.CacheReplay.signWithEncoding` and `Concrete.CacheReplay.topPartFromCache`
are the honest values `keygenChainValueTable` at the signed coordinates (`Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable`,
`Concrete.CacheReplay.topPartFromCache_chainValue_eq_keygenChainValueTable`).
-/

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

/-- The chain values a signature sends at the layer of `key`. -/
def _root_.XmssSecurity.Signature.keyChainValue (signature : Signature) :
    ChainKey → ChainIndex → Digest
  | .inl _ => signature.chainValue
  | .inr _ => signature.top.chainValue

/-- Overwrite one chain value of a signature at the layer of `key`. -/
def replaceSignatureChainValue (key : ChainKey)
    (signature : Signature) (chain : ChainIndex) (value : Digest) : Signature :=
  match key with
  | .inl _ => { signature with chainValue := Function.update signature.chainValue chain value }
  | .inr _ => { signature with
      top := { signature.top with
        chainValue := Function.update signature.top.chainValue chain value } }

@[simp]
theorem replaceSignatureChainValue_same (key : ChainKey)
    (signature : Signature) (chain : ChainIndex) (value : Digest) :
    (replaceSignatureChainValue key signature chain value).keyChainValue key chain = value := by
  cases key <;> simp [replaceSignatureChainValue, Signature.keyChainValue]

theorem replaceSignatureChainValue_other (key : ChainKey)
    (signature : Signature) (chain candidate : ChainIndex) (value : Digest)
    (hne : candidate ≠ chain) :
    (replaceSignatureChainValue key signature chain value).keyChainValue key candidate =
      signature.keyChainValue key candidate := by
  cases key <;> simp [replaceSignatureChainValue, Signature.keyChainValue, Function.update_of_ne hne]

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
