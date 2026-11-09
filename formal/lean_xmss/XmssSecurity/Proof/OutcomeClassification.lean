module

public import XmssSecurity.Proof.ConcreteCorrectness
public import XmssSecurity.Proof.DetailedExecution

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped BigOperators

namespace XmssSecurity

def SigningTranscript.Returned (log : QueryLog SigningSpec)
    (request : SignRequest) (signature : Signature) : Prop :=
  ∃ entry ∈ log, entry.1 = request ∧ entry.2 = some signature

structure ConcreteOutcomeConsistent (cache : QueryCache HashSpec)
    (outcome : GameOutcome) : Prop where
  key : outcome.publicKey =
    Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey
  verification : outcome.verified = Concrete.verifyFromCache cache outcome.publicKey
    outcome.forgery.leafIndex outcome.forgery.message outcome.forgery.signature
  signing : ∀ request signature, SigningTranscript.Returned outcome.signingLog request signature →
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding cache outcome.secretKey
        request.leafIndex signature.randomness encoding
  /-- Every top signature key generation computed decodes, in the cache, on its bottom root. -/
  topSigned : ∀ key randomness encoding,
    outcome.secretKey.topSigned key = some (randomness, encoding) →
      TargetSum.decodeDigest
        (Concrete.CacheView.topEncodingHash cache outcome.secretKey.parameter key
          (Concrete.bottomRoot cache outcome.secretKey key, randomness)) = some encoding

noncomputable def OutcomeBadEventOccurs (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (event : BadEvent) : Prop :=
  outcome.verified = true ∧
  ((∃ request signature signedEncoding forgedEncoding,
    ∃ hsignedEncoding : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.leafIndex
        (request.message, signature.randomness)) = some signedEncoding,
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some forgedEncoding ∧
    SigningTranscript.Returned outcome.signingLog request signature ∧
    request.leafIndex = outcome.forgery.leafIndex ∧
    Concrete.SameLeafIndexBadEventOccurs cache outcome.secretKey.parameter request.leafIndex
      request.message outcome.forgery.message signedEncoding forgedEncoding
      signature outcome.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event) ∨
  (∃ forgedEncoding,
    ∃ hforgedValid : TargetSum.Valid forgedEncoding,
    (¬ ∃ request signature,
      SigningTranscript.Returned outcome.signingLog request signature ∧
        request.leafIndex = outcome.forgery.leafIndex) ∧
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter outcome.forgery.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some forgedEncoding ∧
    Concrete.FreshLeafIndexBadEventOccurs cache outcome.secretKey.parameter
      outcome.forgery.leafIndex forgedEncoding outcome.forgery.signature
      (outcome.secretKey.chainStart outcome.forgery.leafIndex)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding cache outcome.secretKey
          outcome.forgery.leafIndex outcome.forgery.signature.randomness forgedEncoding))
      hforgedValid event))

/-- A top-layer bad event of the forgery: its bottom layer decodes and reaches a root, and its top
signature of that root is an accepted strong forgery of the top key or its tree's top signature. -/
noncomputable def OutcomeTopBadEventOccurs (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (event : BadEvent) : Prop :=
  outcome.verified = true ∧
  ∃ encoding forgedTopEncoding,
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter outcome.forgery.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
    let root := Merkle.ascend
      (Concrete.CacheView.nodeHash cache outcome.secretKey.parameter outcome.forgery.leafIndex)
      (Concrete.signaturePath outcome.forgery.signature) 0 treeHeight
      (Concrete.CacheView.leafHash cache outcome.secretKey.parameter outcome.forgery.leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep cache outcome.secretKey.parameter
            outcome.forgery.leafIndex chain) encoding outcome.forgery.signature.chainValue))
    TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash cache outcome.secretKey.parameter
        (topKeyOf outcome.forgery.leafIndex) (root, outcome.forgery.signature.top.randomness)) =
        some forgedTopEncoding ∧
    Concrete.TopBadEventOccurs cache outcome.secretKey (topKeyOf outcome.forgery.leafIndex) root
      outcome.forgery.signature.top forgedTopEncoding event

/-- An accepted top signature of a bottom root is a top-layer bad event, or the honest top signature
of the honest bottom root. -/
theorem top_badEvent_or_honest (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (htopSigned : ∀ key randomness encoding,
      secretKey.topSigned key = some (randomness, encoding) →
        TargetSum.decodeDigest
          (Concrete.CacheView.topEncodingHash cache secretKey.parameter key
            (Concrete.bottomRoot cache secretKey key, randomness)) = some encoding)
    (key : TopIndex) (root : Digest) (part : LayerSignature)
    (hverify : Concrete.verifyTopFromCache cache
      (Concrete.CacheReplay.publicKeyFromCache cache secretKey) key root part = true) :
    (∃ encoding event,
      TargetSum.decodeDigest
        (Concrete.CacheView.topEncodingHash cache secretKey.parameter key (root, part.randomness)) =
          some encoding ∧
      Concrete.TopBadEventOccurs cache secretKey key root part encoding event) ∨
    (root = Concrete.bottomRoot cache secretKey key ∧
      part = Concrete.CacheReplay.topPartFromCache cache secretKey key ∧
      (secretKey.topSigned key).isSome) := by
  have hpk : Concrete.CacheReplay.publicKeyFromCache cache secretKey =
      ⟨Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
        treeHeight Concrete.rootNode, secretKey.parameter⟩ := by
    rw [Concrete.CacheReplay.publicKeyFromCache]
  obtain ⟨forgedEncoding, hforgedEncoding, hforgedRoot⟩ :=
    (Concrete.verifyTopFromCache_eq_true_iff _ _ _ _ _).mp hverify
  rw [hpk] at hforgedEncoding hforgedRoot
  dsimp only at hforgedEncoding hforgedRoot
  have hforgedValid := (TargetSum.decodeDigest_eq_some_iff.mp hforgedEncoding).2
  cases hsigned : secretKey.topSigned key with
  | some signed =>
      obtain ⟨randomness, encoding⟩ := signed
      have hdecode := htopSigned key randomness encoding hsigned
      obtain ⟨hpart, -⟩ := Concrete.CacheReplay.layerPath_topPartFromCache cache secretKey key
        randomness encoding hsigned
      have hhonestRoot :
          Merkle.ascend (Concrete.CacheView.topNodeHash cache secretKey.parameter key)
              (Concrete.honestTopPath cache secretKey key) 0 treeHeight
              (Concrete.CacheView.topLeafHash cache secretKey.parameter key
                (recoveredEndpoints
                  (fun chain => Concrete.CacheView.topChainStep cache secretKey.parameter key chain)
                  encoding (Concrete.honestTopValues cache secretKey key encoding))) =
            Concrete.CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart
              treeHeight Concrete.rootNode := by
        rw [Concrete.CacheReplay.recover_honestTopValues]
        exact Concrete.CacheReplay.honestTopPath_ascends_to_root cache secretKey key
      by_cases hsame : (Concrete.bottomRoot cache secretKey key, randomness) =
            (root, part.randomness) ∧
          Concrete.honestTopValues cache secretKey key encoding = part.chainValue ∧
          Merkle.SamePathSegment (Concrete.honestTopPath cache secretKey key)
            (Concrete.layerPath part) 0 treeHeight
      · obtain ⟨hinput, hvalues, hpath⟩ := hsame
        simp only [Prod.mk.injEq] at hinput
        refine Or.inr ⟨hinput.1.symm, ?_, by simp⟩
        rw [hpart]
        obtain ⟨partRandomness, partValues, partPath⟩ := part
        dsimp only at hinput hvalues
        rw [hinput.2, hvalues, LayerSignature.mk.injEq]
        refine ⟨rfl, rfl, ?_⟩
        funext level
        have hlevel := hpath level.val level.isLt
        simp only [Nat.zero_add, Concrete.layerPath, level.isLt, ↓reduceDIte] at hlevel
        exact hlevel.symm
      · have hstrong : (Concrete.bottomRoot cache secretKey key, randomness) ≠
              (root, part.randomness) ∨
            Concrete.honestTopValues cache secretKey key encoding ≠ part.chainValue ∨
            ¬Merkle.SamePathSegment (Concrete.honestTopPath cache secretKey key)
              (Concrete.layerPath part) 0 treeHeight := by
          simpa only [not_and_or] using hsame
        obtain ⟨event, hevent⟩ := XmssSecurity.sameLeafIndex_forgery_has_badEvent
          (Concrete.CacheView.topEncodingHash cache secretKey.parameter key)
          (fun chain => Concrete.CacheView.topChainStep cache secretKey.parameter key chain)
          (Concrete.CacheView.topLeafHash cache secretKey.parameter key)
          (Concrete.CacheView.topNodeHash cache secretKey.parameter key)
          (Concrete.bottomRoot cache secretKey key, randomness) (root, part.randomness)
          encoding forgedEncoding
          (Concrete.honestTopValues cache secretKey key encoding) part.chainValue
          (Concrete.honestTopPath cache secretKey key) (Concrete.layerPath part)
          hdecode hforgedEncoding (hforgedRoot.trans hhonestRoot.symm) hstrong
        refine Or.inl ⟨forgedEncoding, event, hforgedEncoding, ?_⟩
        unfold Concrete.TopBadEventOccurs
        rw [hsigned]
        exact ⟨_, hevent⟩
  | none =>
      have hhonestRoot := Concrete.CacheReplay.honestTopPath_ascends_to_root cache secretKey key
      obtain ⟨event, hevent⟩ := XmssSecurity.freshLeafIndex_forgery_has_badEvent
        (fun chain => Concrete.CacheView.topChainStep cache secretKey.parameter key chain)
        (Concrete.CacheView.topLeafHash cache secretKey.parameter key)
        (Concrete.CacheView.topNodeHash cache secretKey.parameter key)
        forgedEncoding part.chainValue (secretKey.topChainStart key)
        (Concrete.layerPath part) (Concrete.honestTopPath cache secretKey key) hforgedValid
        (hforgedRoot.trans hhonestRoot.symm)
      refine Or.inl ⟨forgedEncoding, event, hforgedEncoding, ?_⟩
      unfold Concrete.TopBadEventOccurs
      rw [hsigned]
      exact ⟨hforgedValid, hevent⟩

/-- Every consistent winning execution has one of the concrete cache-level bad events, of the bottom
layer or of the top. -/
theorem winning_outcome_has_badEvent (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (hconsistent : ConcreteOutcomeConsistent cache outcome)
    (hwin : outcome.won = true) :
    ∃ event, OutcomeBadEventOccurs cache outcome event ∨
      OutcomeTopBadEventOccurs cache outcome event := by
  obtain ⟨_, hnotContains, hverifed⟩ := outcome.won_eq_true_iff.mp hwin
  have hforgedVerify :
      Concrete.verifyFromCache cache outcome.publicKey outcome.forgery.leafIndex
        outcome.forgery.message outcome.forgery.signature = true := by
    rw [← hconsistent.verification]
    exact hverifed
  rw [hconsistent.key] at hforgedVerify
  have hparam : (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey).parameter =
      outcome.secretKey.parameter := by
    rw [Concrete.CacheReplay.publicKeyFromCache]
  obtain ⟨forgedEncoding, hforgedEncoding, htopVerify⟩ :=
    (Concrete.verifyFromCache_eq_true_iff cache
      (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey)
      outcome.forgery.leafIndex outcome.forgery.message outcome.forgery.signature).mp
      hforgedVerify
  rw [hparam] at hforgedEncoding htopVerify
  rcases top_badEvent_or_honest cache outcome.secretKey hconsistent.topSigned
      (topKeyOf outcome.forgery.leafIndex) _ outcome.forgery.signature.top htopVerify with
    ⟨topEncoding, event, htopEncoding, hevent⟩ | ⟨hrootEq, htopEq, hisSome⟩
  · exact ⟨event, Or.inr ⟨hverifed, forgedEncoding, topEncoding, hforgedEncoding, htopEncoding,
      hevent⟩⟩
  by_cases hsigned : ∃ request signature,
      SigningTranscript.Returned outcome.signingLog request signature ∧
      request.leafIndex = outcome.forgery.leafIndex
  · obtain ⟨request, signature, hentry, hleafIndex⟩ := hsigned
    obtain ⟨signedEncoding, hsignedEncoding, hsignature⟩ :=
      hconsistent.signing request signature hentry
    obtain ⟨⟨topRandomness, topSignedEncoding⟩, htopSigned⟩ :=
      Option.isSome_iff_exists.mp hisSome
    have hsignedVerify :
        Concrete.verifyFromCache cache
          (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey)
          request.leafIndex request.message signature = true := by
      rw [hsignature]
      refine Concrete.CacheReplay.verifyFromCache_signWithEncoding cache outcome.secretKey
        request.leafIndex request.message signature.randomness signedEncoding hsignedEncoding
        ⟨topRandomness, topSignedEncoding, ?_, ?_⟩
      · rw [hleafIndex]
        exact htopSigned
      · rw [hleafIndex]
        exact hconsistent.topSigned _ _ _ htopSigned
    have hstrong : request.message ≠ outcome.forgery.message ∨
        signature ≠ outcome.forgery.signature := by
      by_contra hsame
      push Not at hsame
      apply hnotContains
      obtain ⟨entry, hmem, hrequest, hsignatureEntry⟩ := hentry
      refine ⟨entry, hmem, ?_, ?_⟩
      · rw [hrequest]
        exact congrArg₂ SignRequest.mk hleafIndex hsame.1
      · rw [hsignatureEntry]
        exact congrArg some hsame.2
    have htop : signature.top = outcome.forgery.signature.top := by
      rw [htopEq, hsignature, ← hleafIndex]
      rfl
    have hhonestRoot := Concrete.CacheReplay.authenticationPath_ascends_to_root cache
      outcome.secretKey request.leafIndex signature.randomness signedEncoding
    rw [← hleafIndex] at hforgedVerify hforgedEncoding hrootEq
    have hroot :
        Concrete.bottomRootFromCache cache
            (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey) request.leafIndex
            outcome.forgery.message outcome.forgery.signature =
          Concrete.bottomRootFromCache cache
            (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey) request.leafIndex
            request.message signature := by
      unfold Concrete.bottomRootFromCache
      rw [hparam, hforgedEncoding, hsignedEncoding]
      dsimp only
      refine congrArg some (hrootEq.trans ?_)
      rw [hsignature, Concrete.CacheReplay.leafHash_recovered_signWithEncoding]
      exact hhonestRoot.symm
    obtain ⟨actualSignedEncoding, forgedEncoding', hactualSignedEncoding,
      hforgedEncoding', event, hevent⟩ :=
      Concrete.sameLeafIndex_badEvent_of_verifyFromCache cache
        (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey) request.leafIndex
        request.message outcome.forgery.message signature outcome.forgery.signature
        hsignedVerify hforgedVerify hstrong htop hroot
    generalize hp : (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey).parameter = p
      at hactualSignedEncoding hforgedEncoding' hevent
    obtain rfl : p = outcome.secretKey.parameter := hp.symm.trans hparam
    exact ⟨event, Or.inl ⟨hverifed, Or.inl ⟨request, signature, actualSignedEncoding,
      forgedEncoding', hactualSignedEncoding, hforgedEncoding', hentry, hleafIndex, hevent⟩⟩⟩
  · have hhonestRoot := Concrete.CacheReplay.authenticationPath_ascends_to_root cache
      outcome.secretKey outcome.forgery.leafIndex outcome.forgery.signature.randomness
      forgedEncoding
    have hforgedValid := (TargetSum.decodeDigest_eq_some_iff.mp hforgedEncoding).2
    obtain ⟨event, hevent⟩ := Concrete.freshLeafIndex_forgery_has_badEvent cache
      outcome.secretKey.parameter outcome.forgery.leafIndex forgedEncoding
      outcome.forgery.signature (outcome.secretKey.chainStart outcome.forgery.leafIndex)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding cache outcome.secretKey outcome.forgery.leafIndex
          outcome.forgery.signature.randomness forgedEncoding)) hforgedValid
      (hrootEq.trans hhonestRoot.symm)
    exact ⟨event, Or.inl ⟨hverifed, Or.inr ⟨forgedEncoding, hforgedValid, hsigned,
      hforgedEncoding, hevent⟩⟩⟩

end XmssSecurity
