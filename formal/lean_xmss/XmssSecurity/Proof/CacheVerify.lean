module

public import XmssSecurity.Proof.ConcreteForgery
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleSpec

namespace XmssSecurity.Concrete

/-- The bottom root a signature's bottom layer reaches from the message, if its digest decodes. -/
noncomputable def bottomRootFromCache (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) : Option Digest :=
  match TargetSum.decodeDigest
      (CacheView.encodingHash cache publicKey.parameter leafIndex
        (message, signature.randomness)) with
  | none => none
  | some encoding =>
      some (Merkle.ascend (CacheView.nodeHash cache publicKey.parameter leafIndex)
        (signaturePath signature) 0 treeHeight
        (CacheView.leafHash cache publicKey.parameter leafIndex
          (XmssSecurity.recoveredEndpoints
            (fun chain => CacheView.chainStep cache publicKey.parameter leafIndex chain)
            encoding signature.chainValue)))

/-- The top layer's check of a bottom root against the public root. -/
noncomputable def verifyTopFromCache (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (key : TopIndex) (root : Digest) (part : LayerSignature) : Bool :=
  match TargetSum.decodeDigest
      (CacheView.topEncodingHash cache publicKey.parameter key (root, part.randomness)) with
  | none => false
  | some encoding =>
      decide (Merkle.ascend (CacheView.topNodeHash cache publicKey.parameter key)
        (layerPath part) 0 treeHeight
        (CacheView.topLeafHash cache publicKey.parameter key
          (XmssSecurity.recoveredEndpoints
            (fun chain => CacheView.topChainStep cache publicKey.parameter key chain)
            encoding part.chainValue)) = publicKey.root)

noncomputable def verifyFromCache (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) : Bool :=
  match bottomRootFromCache cache publicKey leafIndex message signature with
  | none => false
  | some root => verifyTopFromCache cache publicKey (topKeyOf leafIndex) root signature.top

theorem verifyTopFromCache_eq_true_iff (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (key : TopIndex) (root : Digest) (part : LayerSignature) :
    verifyTopFromCache cache publicKey key root part = true ↔
      ∃ encoding,
        TargetSum.decodeDigest
          (CacheView.topEncodingHash cache publicKey.parameter key (root, part.randomness)) =
            some encoding ∧
        Merkle.ascend (CacheView.topNodeHash cache publicKey.parameter key)
          (layerPath part) 0 treeHeight
          (CacheView.topLeafHash cache publicKey.parameter key
            (XmssSecurity.recoveredEndpoints
              (fun chain => CacheView.topChainStep cache publicKey.parameter key chain)
              encoding part.chainValue)) = publicKey.root := by
  unfold verifyTopFromCache
  split <;> rename_i hdecode
  · simp only [Bool.false_eq_true, false_iff]
    rintro ⟨encoding, hencoding, _⟩
    rw [hdecode] at hencoding
    cases hencoding
  · simp only [decide_eq_true_eq]
    constructor
    · intro hroot
      exact ⟨_, hdecode, hroot⟩
    · rintro ⟨encoding, hencoding, hroot⟩
      rw [hdecode] at hencoding
      cases hencoding
      exact hroot

theorem verifyFromCache_eq_true_iff (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) :
    verifyFromCache cache publicKey leafIndex message signature = true ↔
      ∃ encoding,
        TargetSum.decodeDigest
          (CacheView.encodingHash cache publicKey.parameter leafIndex
            (message, signature.randomness)) = some encoding ∧
        verifyTopFromCache cache publicKey (topKeyOf leafIndex)
          (Merkle.ascend (CacheView.nodeHash cache publicKey.parameter leafIndex)
            (signaturePath signature) 0 treeHeight
            (CacheView.leafHash cache publicKey.parameter leafIndex
              (XmssSecurity.recoveredEndpoints
                (fun chain => CacheView.chainStep cache publicKey.parameter leafIndex chain)
                encoding signature.chainValue))) signature.top = true := by
  unfold verifyFromCache bottomRootFromCache
  split <;> rename_i hroot
  · split at hroot <;> rename_i hdecode
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨encoding, hencoding, _⟩
      rw [hdecode] at hencoding
      cases hencoding
    · cases hroot
  · split at hroot <;> rename_i hdecode
    · cases hroot
    · cases hroot
      constructor
      · intro htop
        exact ⟨_, hdecode, htop⟩
      · rintro ⟨encoding, hencoding, htop⟩
        rw [hdecode] at hencoding
        cases hencoding
        exact htop

/-- Two distinct accepted openings at one leaf index yield a concrete cache-level bad event. -/
theorem sameLeafIndex_badEvent_of_verifyFromCache
    (cache : QueryCache HashSpec) (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedSignature forgedSignature : Signature)
    (hsigned : verifyFromCache cache publicKey leafIndex signedMessage signedSignature = true)
    (hforged : verifyFromCache cache publicKey leafIndex forgedMessage forgedSignature = true)
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature)
    (htop : signedSignature.top = forgedSignature.top)
    (hroot : bottomRootFromCache cache publicKey leafIndex forgedMessage forgedSignature =
      bottomRootFromCache cache publicKey leafIndex signedMessage signedSignature) :
    ∃ signedEncoding forgedEncoding,
      ∃ hsignedEncoding : TargetSum.decodeDigest
        (CacheView.encodingHash cache publicKey.parameter leafIndex
          (signedMessage, signedSignature.randomness)) = some signedEncoding,
      ∃ _hforgedEncoding : TargetSum.decodeDigest
        (CacheView.encodingHash cache publicKey.parameter leafIndex
          (forgedMessage, forgedSignature.randomness)) = some forgedEncoding,
      ∃ event, SameLeafIndexBadEventOccurs cache publicKey.parameter leafIndex
        signedMessage forgedMessage signedEncoding forgedEncoding
        signedSignature forgedSignature
        (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  obtain ⟨signedEncoding, hsignedEncoding, -⟩ :=
    (verifyFromCache_eq_true_iff cache publicKey leafIndex signedMessage signedSignature).mp hsigned
  obtain ⟨forgedEncoding, hforgedEncoding, -⟩ :=
    (verifyFromCache_eq_true_iff cache publicKey leafIndex forgedMessage forgedSignature).mp hforged
  unfold bottomRootFromCache at hroot
  rw [hsignedEncoding, hforgedEncoding] at hroot
  obtain ⟨event, hevent⟩ := Concrete.sameLeafIndex_forgery_has_badEvent
    cache publicKey.parameter leafIndex signedMessage forgedMessage
    signedEncoding forgedEncoding signedSignature forgedSignature
    hsignedEncoding hforgedEncoding (Option.some.inj hroot) hstrong htop
  exact ⟨signedEncoding, forgedEncoding, hsignedEncoding, hforgedEncoding, event, hevent⟩

end XmssSecurity.Concrete
