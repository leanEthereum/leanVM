import XmssSecurity.Proof.ExpectedAdaptiveFreshTarget
import XmssSecurity.Proof.CappedDetailedQueryPresence
import XmssSecurity.Proof.CappedSigningLogReplay
import XmssSecurity.Proof.LeafTargetInput

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedLeaf


/-- Map a leaf input to the honest leaf input fixed by key generation at the same leaf index. -/
noncomputable def keygenLeafTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ leafIndex endpoints,
      input = Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints then
    Concrete.CacheView.leafInput secretKey.parameter h.choose
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart h.choose)
  else input

@[simp]
theorem keygenLeafTargetInput_leafInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
      Concrete.CacheView.leafInput secretKey.parameter leafIndex
        (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
          secretKey.chainStart leafIndex) := by
  unfold keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨chosenEndpoints, hinput⟩ := h.choose_spec
    have hleafIndex : h.choose = leafIndex := by
      have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
        (hinput.trans rfl)
      simp only [HashDomain.leaf.injEq] at hdomain
      exact hdomain.symm
    rw [hleafIndex]
  · rename_i h
    exfalso
    exact h ⟨leafIndex, endpoints, rfl⟩

attribute [irreducible] keygenLeafTargetInput

theorem detailedGameAfterKeygen_keys_eq
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey)).run
          initialCache)) :
    execution.1.publicKey = publicKey ∧ execution.1.secretKey = secretKey := by
  unfold detailedGameAfterKeygen at hmem
  simp only at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  exact ⟨rfl, rfl⟩

/-- Cache facts for one leaf collision assemble into the adaptive fresh-collision predicate. -/
theorem adaptiveFreshDigestCollisionWith_of_leafCollision
    (secretKey : SecretKey) (initialCache finalCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (forgedEndpoints : ChainIndex → Digest)
    (forgedOutput honestOutput : HashOutput)
    (hforgedFinal : finalCache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex forgedEndpoints) =
        some forgedOutput)
    (hforgedInitial : initialCache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex forgedEndpoints) = none)
    (hhonestInitial : initialCache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex
        (Concrete.CacheReplay.oneTimePublicKey initialCache secretKey.parameter
          secretKey.chainStart leafIndex)) = some honestOutput)
    (hhonestFinal : finalCache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex
        (Concrete.CacheReplay.oneTimePublicKey initialCache secretKey.parameter
          secretKey.chainStart leafIndex)) = some honestOutput)
    (hstable : Concrete.CacheReplay.oneTimePublicKey finalCache secretKey.parameter
        secretKey.chainStart leafIndex =
      Concrete.CacheReplay.oneTimePublicKey initialCache secretKey.parameter
        secretKey.chainStart leafIndex)
    (hleafEquality : Concrete.CacheView.leafHash finalCache secretKey.parameter leafIndex
        forgedEndpoints =
      Concrete.CacheView.leafHash finalCache secretKey.parameter leafIndex
        (Concrete.CacheReplay.oneTimePublicKey finalCache secretKey.parameter
          secretKey.chainStart leafIndex)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenLeafTargetInput secretKey initialCache) := by
  let forgedInput := Concrete.CacheView.leafInput secretKey.parameter leafIndex forgedEndpoints
  refine ⟨forgedInput, forgedOutput, honestOutput, hforgedFinal, hforgedInitial, ?_, ?_⟩
  · rw [show forgedInput = Concrete.CacheView.leafInput secretKey.parameter leafIndex
      forgedEndpoints by rfl]
    rw [keygenLeafTargetInput_leafInput]
    exact hhonestInitial
  · rw [show forgedInput = Concrete.CacheView.leafInput secretKey.parameter leafIndex
      forgedEndpoints by rfl]
    rw [keygenLeafTargetInput_leafInput]
    rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedFinal,
      Concrete.CacheView.digestAt_eq_of_cache_eq_some hhonestFinal]
    unfold Concrete.CacheView.leafHash at hleafEquality
    rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedFinal] at hleafEquality
    rw [hstable, Concrete.CacheView.digestAt_eq_of_cache_eq_some hhonestFinal] at hleafEquality
    exact hleafEquality

/-- A final-cache leaf collision against the honest WOTS public key is fresh after key generation. -/
theorem leafCollision_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (leafIndex : LeafIndex) (forgedEndpoints : ChainIndex → Digest) (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex forgedEndpoints) =
        some forgedOutput)
    (hleafCollision : Wots.HasLeafCollision
      (Concrete.CacheView.leafHash execution.2 secretKey.parameter leafIndex)
      forgedEndpoints
      (Concrete.CacheReplay.oneTimePublicKey execution.2 secretKey.parameter
        secretKey.chainStart leafIndex)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  have hafterCacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
  have holdKeygen : oldKeyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅) :=
    Concrete.precomputedKeygen_support_oldKeygen keyResult hkeygen'
  have honeTimeStable := (Concrete.keygen_oneTimePublicKey_eq_of_cache_le oldKeyResult
    holdKeygen execution.2 hafterCacheLe leafIndex).symm
  change Concrete.CacheReplay.oneTimePublicKey execution.2 keyResult.1.2.parameter
      keyResult.1.2.chainStart leafIndex =
    Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
      keyResult.1.2.chainStart leafIndex at honeTimeStable
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.keygen_cache_has_leafInput oldKeyResult holdKeygen leafIndex
  change keyResult.2
      (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex
        (Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart leafIndex)) = some honestOutput at hhonestCached
  have hforgedInitial : keyResult.2
      (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex forgedEndpoints) = none := by
    apply Concrete.keygen_cache_leafInput_eq_none_of_ne oldKeyResult holdKeygen leafIndex
      forgedEndpoints
    intro heq
    apply hleafCollision.1
    exact heq.trans honeTimeStable.symm
  exact adaptiveFreshDigestCollisionWith_of_leafCollision keyResult.1.2 keyResult.2
    execution.2 leafIndex forgedEndpoints forgedOutput honestOutput hforgedCached hforgedInitial
    hhonestCached (hafterCacheLe hhonestCached) honeTimeStable hleafCollision.2

/-- The leaf branch of a concrete fresh-leaf-index event is exactly a collision with the honest WOTS public key. -/
theorem fresh_leaf_badEvent_is_collision
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (honestPath : Nat → Digest) (hforgedValid : TargetSum.Valid forgedEncoding)
    (hevent : Concrete.FreshLeafIndexBadEventOccurs cache secretKey.parameter leafIndex
      forgedEncoding forgedSignature (secretKey.chainStart leafIndex) honestPath
      hforgedValid .leaf) :
    Wots.HasLeafCollision
      (Concrete.CacheView.leafHash cache secretKey.parameter leafIndex)
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
        forgedEncoding forgedSignature.chainValue)
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart leafIndex) := by
  change Wots.HasLeafCollision
    (Concrete.CacheView.leafHash cache secretKey.parameter leafIndex)
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
      forgedEncoding forgedSignature.chainValue)
    (fun chain => Wots.walk
      (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain) 0
      (chainLength - 1) (secretKey.chainStart leafIndex chain))
  simpa [Concrete.FreshLeafIndexBadEventOccurs, XmssSecurity.FreshLeafIndexBadEventOccurs,
    Wots.publicChain] using hevent

/-- A successful detailed execution caches the forged leaf for its uniquely decoded encoding. -/
theorem detailed_execution_verified_leaf_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding) :
    ∃ output, execution.2
      (Concrete.CacheView.leafInput execution.1.secretKey.parameter execution.1.forgery.leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
          encoding execution.1.forgery.signature.chainValue)) = some output := by
  obtain ⟨actualEncoding, output, hactualDecode, hcached⟩ :=
    capped_detailed_execution_verified_leaf_cached adversary execution hgame hverified
  have hencoding : actualEncoding = encoding := by
    rw [hdecode] at hactualDecode
    exact Option.some.inj hactualDecode.symm
  subst actualEncoding
  exact ⟨output, hcached⟩

/-- A supported fresh leaf witness supplies both the verifier query and its concrete leaf collision. -/
theorem fresh_leaf_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 .leaf)
    (hfresh : ∃ forgedEncoding,
      ∃ hforgedValid : TargetSum.Valid forgedEncoding,
      (¬ ∃ request signature,
        SigningTranscript.Returned execution.1.signingLog request signature ∧
          request.leafIndex = execution.1.forgery.leafIndex) ∧
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex
          (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some forgedEncoding ∧
      Concrete.FreshLeafIndexBadEventOccurs execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex forgedEncoding execution.1.forgery.signature
        (execution.1.secretKey.chainStart execution.1.forgery.leafIndex)
        (Concrete.signaturePath
          (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
            execution.1.forgery.leafIndex execution.1.forgery.signature.randomness forgedEncoding))
        hforgedValid .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hleafEvent⟩ := hfresh
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1
    keyResult.1.2 keyResult.2 execution hafter
  have hgame : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary) := by
    unfold detailedGameWithCache detailedGameCore
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨keyResult, hkeygen, hafter⟩
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_leaf_cached_as adversary execution hgame
      forgedEncoding hevent.1 hforgedDecode
  let forgedEndpoints := recoveredEndpoints
    (fun chain => Concrete.CacheView.chainStep execution.2
      execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
    forgedEncoding execution.1.forgery.signature.chainValue
  apply leafCollision_afterKeygen_orientation adversary keyResult hkeygen execution
    hafter execution.1.secretKey hkeys.2 execution.1.forgery.leafIndex
      forgedEndpoints forgedOutput
  · simpa [forgedEndpoints] using hforgedCached
  · exact fresh_leaf_badEvent_is_collision execution.2 execution.1.secretKey
      execution.1.forgery.leafIndex forgedEncoding execution.1.forgery.signature
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.leafIndex execution.1.forgery.signature.randomness
          forgedEncoding)) hforgedValid hleafEvent


theorem signed_recoveredEndpoints_eq_oneTimePublicKey
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (signature : Signature) (encoding : Encoding)
    (hsignature : signature = Concrete.CacheReplay.signWithEncoding cache secretKey
      leafIndex signature.randomness encoding) :
    recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding signature.chainValue =
      Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart leafIndex := by
  rw [hsignature]
  funext chain
  change Wots.recoverChain
      (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
      (encoding chain)
      (Wots.signChain (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
        (encoding chain) (secretKey.chainStart leafIndex chain)) =
    Wots.publicChain (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
      (secretKey.chainStart leafIndex chain)
  exact Wots.recover_signChain_eq_publicChain _ _ _

theorem same_leaf_badEvent_is_collision
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (request : SignRequest)
    (signature forgedSignature : Signature) (forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedValid : TargetSum.Valid signedEncoding)
    (hsignature : signature = Concrete.CacheReplay.signWithEncoding cache secretKey
      request.leafIndex signature.randomness signedEncoding)
    (hevent : Concrete.SameLeafIndexBadEventOccurs cache secretKey.parameter request.leafIndex
      request.message forgedMessage signedEncoding forgedEncoding signature forgedSignature
      hsignedValid .leaf) :
    Wots.HasLeafCollision
      (Concrete.CacheView.leafHash cache secretKey.parameter request.leafIndex)
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter
          request.leafIndex chain)
        forgedEncoding forgedSignature.chainValue)
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart request.leafIndex) := by
  change Wots.HasLeafCollision
    (Concrete.CacheView.leafHash cache secretKey.parameter request.leafIndex)
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain)
      forgedEncoding forgedSignature.chainValue)
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain)
      signedEncoding signature.chainValue) at hevent
  rw [signed_recoveredEndpoints_eq_oneTimePublicKey cache secretKey request.leafIndex
    signature signedEncoding hsignature] at hevent
  exact hevent

theorem detailed_execution_returned_signature_eq
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex (request.message, signature.randomness)) = some encoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature) :
    signature = Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
      request.leafIndex signature.randomness encoding := by
  obtain ⟨actualEncoding, hactualDecode, hsignature⟩ :=
    (capped_detailed_execution_consistent adversary execution hgame).signing request signature hreturned
  have hencoding : actualEncoding = encoding := by
    rw [hdecode] at hactualDecode
    exact Option.some.inj hactualDecode.symm
  subst actualEncoding
  exact hsignature

theorem afterKeygen_execution_mem_detailedGame
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2)) :
    execution ∈ support (detailedGameWithCache Concrete.scheme adversary) := by
  unfold detailedGameWithCache detailedGameCore
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨keyResult, hkeygen, hafter⟩

theorem same_leaf_witness_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (request : SignRequest) (signature : Signature)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex (request.message, signature.randomness)) = some signedEncoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature)
    (hleafIndex : request.leafIndex = execution.1.forgery.leafIndex)
    (hleafEvent : Concrete.SameLeafIndexBadEventOccurs execution.2
      execution.1.secretKey.parameter request.leafIndex request.message
      execution.1.forgery.message signedEncoding forgedEncoding signature
      execution.1.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hgame := afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hafter
  have hsignature := detailed_execution_returned_signature_eq adversary execution hgame
    request signature signedEncoding hsignedDecode hreturned
  have hdecodeLeafIndex := congrArg (fun leafIndex => TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter leafIndex
      (execution.1.forgery.message, execution.1.forgery.signature.randomness))) hleafIndex
  have hforgedDecode' : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding := hdecodeLeafIndex.symm.trans hforgedDecode
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    capped_detailed_execution_verified_leaf_cached_as adversary execution hgame forgedEncoding
      hverified hforgedDecode'
  have hleafCollision := same_leaf_badEvent_is_collision execution.2
    execution.1.secretKey request signature execution.1.forgery.signature
    execution.1.forgery.message signedEncoding forgedEncoding
    (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 hsignature hleafEvent
  rw [hleafIndex] at hleafCollision
  exact leafCollision_afterKeygen_orientation adversary keyResult hkeygen execution
    hafter execution.1.secretKey hkeys.2 execution.1.forgery.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
        forgedEncoding execution.1.forgery.signature.chainValue)
      forgedOutput hforgedCached hleafCollision

theorem leaf_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hleafEvent⟩ := hsame
    exact same_leaf_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 request signature signedEncoding forgedEncoding hsignedDecode
      hforgedDecode hreturned hleafIndex hleafEvent
  · exact fresh_leaf_event_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent hfresh

end XmssSecurity.CappedLeaf
