import XmssSecurity.Proof.Merkle
import XmssSecurity.Proof.SecurityBudget
import XmssSecurity.Proof.WotsExtraction

namespace XmssSecurity

def recoveredEndpoints (step : ChainIndex → Nat → Digest → Digest)
    (encoding : Encoding) (values : ChainIndex → Digest) : ChainIndex → Digest :=
  fun i => Wots.recoverChain (step i) (encoding i) (values i)

noncomputable def SameLeafIndexBadEventOccurs {EncodingInput : Type}
    (encodingHash : EncodingInput → Digest)
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (signedInput forgedInput : EncodingInput)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → Digest)
    (signedPath forgedPath : Nat → Digest)
    (hsignedValid : TargetSum.Valid signedEncoding) : BadEvent → Prop
  | .encoding => signedInput ≠ forgedInput ∧ encodingHash signedInput = encodingHash forgedInput
  | .chain chain =>
      Wots.IsBackwardWitnessAt step signedEncoding forgedEncoding signedValue forgedValue chain
  | .suffixCollision slot =>
      ∃ position : TargetSum.SuffixPosition signedEncoding,
        TargetSum.enumerateSuffixPositions signedEncoding hsignedValid position = slot ∧
        Wots.IsSuffixCollisionAt step signedEncoding forgedEncoding signedValue forgedValue position
  | .leaf => Wots.HasLeafCollision leafHash
      (recoveredEndpoints step forgedEncoding forgedValue)
      (recoveredEndpoints step signedEncoding signedValue)
  | .merkle level => Merkle.IsXmssPathCollisionAt nodeHash forgedPath signedPath
      (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
      (leafHash (recoveredEndpoints step signedEncoding signedValue)) level

/-- The deterministic core of the same-leaf-index strong-forgery reduction. -/
theorem classify_sameLeafIndex_forgery {EncodingInput : Type}
    (encodingHash : EncodingInput → Digest)
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (signedInput forgedInput : EncodingInput)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → Digest)
    (signedPath forgedPath : Nat → Digest)
    (hsignedEncoding : TargetSum.decodeDigest (encodingHash signedInput) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest (encodingHash forgedInput) = some forgedEncoding)
    (hroot : Merkle.ascend nodeHash forgedPath 0 treeHeight
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue)) =
      Merkle.ascend nodeHash signedPath 0 treeHeight
        (leafHash (recoveredEndpoints step signedEncoding signedValue)))
    (hstrong : signedInput ≠ forgedInput ∨ signedValue ≠ forgedValue ∨
      ¬Merkle.SamePathSegment signedPath forgedPath 0 treeHeight) :
    (signedInput ≠ forgedInput ∧ encodingHash signedInput = encodingHash forgedInput) ∨
      Wots.HasBackwardWitness step signedEncoding forgedEncoding signedValue forgedValue ∨
      Wots.HasSuffixCollisionWitness step signedEncoding forgedEncoding signedValue forgedValue ∨
      Wots.HasLeafCollision leafHash
        (recoveredEndpoints step forgedEncoding forgedValue)
        (recoveredEndpoints step signedEncoding signedValue) ∨
      Merkle.HasXmssPathCollision nodeHash forgedPath signedPath
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
        (leafHash (recoveredEndpoints step signedEncoding signedValue)) := by
  classical
  have hsignedValid := (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2
  have hforgedValid := (TargetSum.decodeDigest_eq_some_iff.mp hforgedEncoding).2
  rcases Merkle.sameXmssPath_or_hasCollision nodeHash forgedPath signedPath
      (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
      (leafHash (recoveredEndpoints step signedEncoding signedValue)) hroot with
    ⟨hleaf, hpath⟩ | hmerkle
  · rcases Wots.eq_or_hasLeafCollision leafHash
      (recoveredEndpoints step forgedEncoding forgedValue)
      (recoveredEndpoints step signedEncoding signedValue) hleaf with hendpoints | hleafCollision
    · have hendpoints' : ∀ i,
          Wots.recoverChain (step i) (forgedEncoding i) (forgedValue i) =
            Wots.recoverChain (step i) (signedEncoding i) (signedValue i) := by
        intro i
        exact congrFun hendpoints i
      by_cases hencoding : signedEncoding = forgedEncoding
      · subst forgedEncoding
        by_cases hvalue : signedValue = forgedValue
        · rcases Classical.em (signedInput = forgedInput) with hinput | hinput
          · exfalso
            rcases hstrong with hneInput | hneValue | hnePath
            · exact hneInput hinput
            · exact hneValue hvalue
            · exact hnePath fun offset hoffset => (hpath offset hoffset).symm
          · left
            exact TargetSum.hash_collision_of_same_decodedEncoding encodingHash hinput
              hsignedEncoding hforgedEncoding
        · exact Or.inr <| Or.inr <| Or.inl <|
            Wots.suffixCollision_of_sameEncoding_of_values_ne step signedEncoding
              signedValue forgedValue hvalue hendpoints'
      · rcases Wots.classify_distinct_valid_encodings step signedEncoding forgedEncoding
          signedValue forgedValue hsignedValid hforgedValid hencoding hendpoints' with
        hbackward | hsuffix
        · exact Or.inr <| Or.inl hbackward
        · exact Or.inr <| Or.inr <| Or.inl hsuffix
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hleafCollision
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr hmerkle

/-- Every same-leaf-index strong forgery selects one of the 175 explicitly indexed bad events. -/
theorem sameLeafIndex_forgery_has_badEvent {EncodingInput : Type}
    (encodingHash : EncodingInput → Digest)
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (signedInput forgedInput : EncodingInput)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → Digest)
    (signedPath forgedPath : Nat → Digest)
    (hsignedEncoding : TargetSum.decodeDigest (encodingHash signedInput) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest (encodingHash forgedInput) = some forgedEncoding)
    (hroot : Merkle.ascend nodeHash forgedPath 0 treeHeight
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue)) =
      Merkle.ascend nodeHash signedPath 0 treeHeight
        (leafHash (recoveredEndpoints step signedEncoding signedValue)))
    (hstrong : signedInput ≠ forgedInput ∨ signedValue ≠ forgedValue ∨
      ¬Merkle.SamePathSegment signedPath forgedPath 0 treeHeight) :
    ∃ event, SameLeafIndexBadEventOccurs encodingHash step leafHash nodeHash
      signedInput forgedInput signedEncoding forgedEncoding signedValue forgedValue
      signedPath forgedPath (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  have hsignedValid := (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2
  rcases classify_sameLeafIndex_forgery encodingHash step leafHash nodeHash
      signedInput forgedInput signedEncoding forgedEncoding signedValue forgedValue
      signedPath forgedPath hsignedEncoding hforgedEncoding hroot hstrong with
    hencoding | hbackward | hsuffix | hleaf | hmerkle
  · exact ⟨.encoding, hencoding⟩
  · obtain ⟨chain, hchain⟩ := hbackward
    exact ⟨.chain chain, hchain⟩
  · obtain ⟨position, hposition⟩ := hsuffix
    exact ⟨.suffixCollision (TargetSum.enumerateSuffixPositions signedEncoding hsignedValid position),
      position, rfl, hposition⟩
  · exact ⟨.leaf, hleaf⟩
  · obtain ⟨level, hlevel⟩ := hmerkle
    exact ⟨.merkle level, hlevel⟩

noncomputable def FreshLeafIndexBadEventOccurs
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (forgedEncoding : Encoding)
    (forgedValue secret : ChainIndex → Digest)
    (forgedPath honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding) : BadEvent → Prop
  | .encoding => False
  | .chain chain => Wots.IsFreshChainValueAt step forgedEncoding forgedValue secret chain
  | .suffixCollision slot =>
      ∃ position : TargetSum.SuffixPosition forgedEncoding,
        TargetSum.enumerateSuffixPositions forgedEncoding hforgedValid position = slot ∧
        Wots.IsSuffixCollisionAt step forgedEncoding forgedEncoding
          (fun i => Wots.signChain (step i) (forgedEncoding i) (secret i)) forgedValue position
  | .leaf => Wots.HasLeafCollision leafHash
      (recoveredEndpoints step forgedEncoding forgedValue)
      (fun i => Wots.publicChain (step i) (secret i))
  | .merkle level => Merkle.IsXmssPathCollisionAt nodeHash forgedPath honestPath
      (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
      (leafHash (fun i => Wots.publicChain (step i) (secret i))) level

/-- The deterministic core of the fresh-leaf-index forgery reduction. -/
theorem classify_freshLeafIndex_forgery
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (forgedEncoding : Encoding)
    (forgedValue secret : ChainIndex → Digest)
    (forgedPath honestPath : Nat → Digest)
    (hroot : Merkle.ascend nodeHash forgedPath 0 treeHeight
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue)) =
      Merkle.ascend nodeHash honestPath 0 treeHeight
        (leafHash (fun i => Wots.publicChain (step i) (secret i)))) :
    Wots.HasFreshChainValue step forgedEncoding forgedValue secret ∨
      Wots.HasSuffixCollisionWitness step forgedEncoding forgedEncoding
        (fun i => Wots.signChain (step i) (forgedEncoding i) (secret i)) forgedValue ∨
      Wots.HasLeafCollision leafHash
        (recoveredEndpoints step forgedEncoding forgedValue)
        (fun i => Wots.publicChain (step i) (secret i)) ∨
      Merkle.HasXmssPathCollision nodeHash forgedPath honestPath
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
        (leafHash (fun i => Wots.publicChain (step i) (secret i))) := by
  rcases Merkle.sameXmssPath_or_hasCollision nodeHash forgedPath honestPath
      (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
      (leafHash (fun i => Wots.publicChain (step i) (secret i))) hroot with
    ⟨hleaf, _hpath⟩ | hmerkle
  · rcases Wots.eq_or_hasLeafCollision leafHash
      (recoveredEndpoints step forgedEncoding forgedValue)
      (fun i => Wots.publicChain (step i) (secret i)) hleaf with
      hendpoints | hleafCollision
    · have hendpoints' : ∀ i,
          Wots.recoverChain (step i) (forgedEncoding i) (forgedValue i) =
            Wots.publicChain (step i) (secret i) := by
        intro i
        exact congrFun hendpoints i
      rcases Wots.freshChainValue_or_suffixCollision step forgedEncoding forgedValue secret
          hendpoints' with hchain | hsuffix
      · exact Or.inl hchain
      · exact Or.inr <| Or.inl hsuffix
    · exact Or.inr <| Or.inr <| Or.inl hleafCollision
  · exact Or.inr <| Or.inr <| Or.inr hmerkle

/-- Every fresh-leaf-index forgery selects one of the same 175 indexed bad-event slots. -/
theorem freshLeafIndex_forgery_has_badEvent
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (forgedEncoding : Encoding)
    (forgedValue secret : ChainIndex → Digest)
    (forgedPath honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding)
    (hroot : Merkle.ascend nodeHash forgedPath 0 treeHeight
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue)) =
      Merkle.ascend nodeHash honestPath 0 treeHeight
        (leafHash (fun i => Wots.publicChain (step i) (secret i)))) :
    ∃ event, FreshLeafIndexBadEventOccurs step leafHash nodeHash forgedEncoding forgedValue secret
      forgedPath honestPath hforgedValid event := by
  rcases classify_freshLeafIndex_forgery step leafHash nodeHash forgedEncoding forgedValue secret
      forgedPath honestPath hroot with hchain | hsuffix | hleaf | hmerkle
  · obtain ⟨chain, hchain⟩ := hchain
    exact ⟨.chain chain, hchain⟩
  · obtain ⟨position, hposition⟩ := hsuffix
    exact ⟨.suffixCollision (TargetSum.enumerateSuffixPositions forgedEncoding hforgedValid position),
      position, rfl, hposition⟩
  · exact ⟨.leaf, hleaf⟩
  · obtain ⟨level, hlevel⟩ := hmerkle
    exact ⟨.merkle level, hlevel⟩

end XmssSecurity
