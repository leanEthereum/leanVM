import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.ForgeryCases

open OracleSpec

namespace XmssSecurity.Concrete

theorem same_signaturePath_iff {left right : Signature} :
    Merkle.SamePathSegment (signaturePath left) (signaturePath right) 0 treeHeight ↔
      left.authPath = right.authPath := by
  constructor
  · intro hpath
    funext level
    have heq := hpath level.val level.isLt
    simpa [signaturePath] using heq
  · intro hpath level hlevel
    simp [signaturePath, hlevel, hpath]

theorem strong_components {signedMessage forgedMessage : Message}
    {signedSignature forgedSignature : Signature}
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature)
    (htop : signedSignature.top = forgedSignature.top) :
    (signedMessage, signedSignature.randomness) ≠
        (forgedMessage, forgedSignature.randomness) ∨
      signedSignature.chainValue ≠ forgedSignature.chainValue ∨
      ¬Merkle.SamePathSegment (signaturePath signedSignature)
        (signaturePath forgedSignature) 0 treeHeight := by
  by_cases hinput :
      (signedMessage, signedSignature.randomness) =
        (forgedMessage, forgedSignature.randomness)
  · by_cases hvalues : signedSignature.chainValue = forgedSignature.chainValue
    · right
      right
      intro hpath
      apply hstrong.elim
      · intro hmessage
        exact hmessage (congrArg Prod.fst hinput)
      · intro hsignature
        apply hsignature
        have hauth := same_signaturePath_iff.mp hpath
        cases signedSignature
        cases forgedSignature
        simp_all
    · exact Or.inr (Or.inl hvalues)
  · exact Or.inl hinput

noncomputable def SameLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedValid : TargetSum.Valid signedEncoding) : BadEvent → Prop :=
  XmssSecurity.SameLeafIndexBadEventOccurs
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    (signaturePath signedSignature) (signaturePath forgedSignature)
    hsignedValid

/-- Concrete same-leaf-index strong forgeries select one of the 175 cache-level bad events. -/
theorem sameLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedEncoding : TargetSum.decodeDigest
      (CacheView.encodingHash cache parameter leafIndex
        (signedMessage, signedSignature.randomness)) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest
      (CacheView.encodingHash cache parameter leafIndex
        (forgedMessage, forgedSignature.randomness)) = some forgedEncoding)
    (hroot : Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath forgedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue)) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath signedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            signedEncoding signedSignature.chainValue)))
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature)
    (htop : signedSignature.top = forgedSignature.top) :
    ∃ event, SameLeafIndexBadEventOccurs cache parameter leafIndex
      signedMessage forgedMessage signedEncoding forgedEncoding
      signedSignature forgedSignature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  exact XmssSecurity.sameLeafIndex_forgery_has_badEvent
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    (signaturePath signedSignature) (signaturePath forgedSignature)
    hsignedEncoding hforgedEncoding hroot (strong_components hstrong htop)

noncomputable def FreshLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding) : BadEvent → Prop :=
  XmssSecurity.FreshLeafIndexBadEventOccurs
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    forgedEncoding forgedSignature.chainValue secret
    (signaturePath forgedSignature) honestPath hforgedValid

/-- Concrete fresh-leaf-index forgeries select one of the same 175 cache-level bad events. -/
theorem freshLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding)
    (hroot : Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath forgedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue)) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        honestPath 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (fun chain => Wots.publicChain
            (CacheView.chainStep cache parameter leafIndex chain) (secret chain)))) :
    ∃ event, FreshLeafIndexBadEventOccurs cache parameter leafIndex forgedEncoding
      forgedSignature secret honestPath hforgedValid event := by
  exact XmssSecurity.freshLeafIndex_forgery_has_badEvent
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    forgedEncoding forgedSignature.chainValue secret
    (signaturePath forgedSignature) honestPath hforgedValid hroot

/-! ### The top layer -/

/-- A top layer signature's path as a function of the level. -/
def layerPath (part : LayerSignature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then part.authPath ⟨level, hlevel⟩ else 0

/-- The honest bottom root of tree `b`, replayed from the cache. -/
def bottomRoot (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex) : Digest :=
  CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart treeHeight (bottomRootNode key)

/-- The honest top path of key `b`, replayed from the cache. -/
def honestTopPath (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex)
    (level : Nat) : Digest :=
  if hlevel : level < treeHeight then
    CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart level
      (topPathNode key ⟨level, hlevel⟩)
  else 0

/-- The honest top chain values of key `b` at a codeword, replayed from the cache. -/
def honestTopValues (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex)
    (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => Wots.signChain (CacheView.topChainStep cache secretKey.parameter key chain)
    (encoding chain) (secretKey.topChainStart key chain)

/-- A top-layer bad event for a forged top signature `forged` of bottom root `root` by key `b`,
whose digest decodes to `forgedEncoding`: against the honest top signature of tree `b` if its
grinding succeeded, otherwise against the top key's secrets. -/
noncomputable def TopBadEventOccurs (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (root : Digest) (forged : LayerSignature) (forgedEncoding : Encoding)
    (event : BadEvent) : Prop :=
  match secretKey.topSigned key with
  | some (randomness, encoding) =>
      ∃ hvalid : TargetSum.Valid encoding,
        XmssSecurity.SameLeafIndexBadEventOccurs
          (CacheView.topEncodingHash cache secretKey.parameter key)
          (fun chain => CacheView.topChainStep cache secretKey.parameter key chain)
          (CacheView.topLeafHash cache secretKey.parameter key)
          (CacheView.topNodeHash cache secretKey.parameter key)
          (bottomRoot cache secretKey key, randomness) (root, forged.randomness)
          encoding forgedEncoding
          (honestTopValues cache secretKey key encoding) forged.chainValue
          (honestTopPath cache secretKey key) (layerPath forged) hvalid event
  | none =>
      ∃ hvalid : TargetSum.Valid forgedEncoding,
        XmssSecurity.FreshLeafIndexBadEventOccurs
          (fun chain => CacheView.topChainStep cache secretKey.parameter key chain)
          (CacheView.topLeafHash cache secretKey.parameter key)
          (CacheView.topNodeHash cache secretKey.parameter key)
          forgedEncoding forged.chainValue (secretKey.topChainStart key)
          (layerPath forged) (honestTopPath cache secretKey key) hvalid event

end XmssSecurity.Concrete
