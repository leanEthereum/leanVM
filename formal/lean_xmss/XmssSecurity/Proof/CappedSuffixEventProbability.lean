module

public import XmssSecurity.Proof.ExpectedAdaptiveFreshTarget
public import XmssSecurity.Proof.CappedLeafEventProbability
public import XmssSecurity.Proof.VerificationChainQuery

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedSuffix


theorem detailed_execution_verified_chain_query_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (chain : ChainIndex) (offset : Nat)
    (hoffset : offset < chainLength - 1 - (encoding chain).val) :
    ∃ output, execution.2
      (Concrete.CacheView.chainInput execution.1.secretKey.parameter
        execution.1.forgery.leafIndex chain
        ⟨(encoding chain).val + offset, by omega⟩
        (Wots.walk
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex chain)
          (encoding chain).val offset (execution.1.forgery.signature.chainValue chain))) =
        some output := by
  have hparameter :=
    (capped_detailed_execution_key_components_consistent adversary execution hmem).1
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only at hparameter hverified hdecode ⊢
  subst verified
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message forgery.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  have hdecodePublic : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache publicKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = some encoding := by
    rw [hparameter]
    exact hdecode
  rw [← hparameter]
  exact Concrete.CacheReplay.verify_true_chain_query_cached_as_in_largerCache publicKey
    forgery.leafIndex forgery.message forgery.signature encoding chain offset hoffset
    adversaryCache finalCache finalCache hverify hdecodePublic le_rfl


theorem Wots.walk_signChain_eq_honest (step : Nat → Digest → Digest)
    (digit : Digit) (offset : Nat) (secret : Digest) :
    Wots.walk step digit.val offset (Wots.signChain step digit secret) =
      Wots.walk step 0 (digit.val + offset) secret := by
  simpa only [Wots.signChain, zero_add] using
    (Wots.walk_add step 0 digit.val offset secret).symm

noncomputable def keygenChainTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ address : LeafIndex × ChainIndex × ChainStep, ∃ value,
      input = Concrete.CacheView.chainInput secretKey.parameter address.1
        address.2.1 address.2.2 value then
    let address := h.choose
    Concrete.CacheView.chainInput secretKey.parameter address.1 address.2.1 address.2.2
      (Wots.walk
        (Concrete.CacheView.chainStep cache secretKey.parameter address.1 address.2.1)
        0 address.2.2.val (secretKey.chainStart address.1 address.2.1))
  else input

@[simp]
theorem keygenChainTargetInput_chainInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    keygenChainTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
      Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
        (Wots.walk (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
          0 step.val (secretKey.chainStart leafIndex chain)) := by
  unfold keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨chosenValue, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      (hinput.trans rfl)
    simp only [HashDomain.chain.injEq] at hdomain
    rcases hdomain with ⟨hleafIndex, hchain, hstep⟩
    dsimp only
    rw [← hleafIndex, ← hchain, ← hstep]
  · rename_i h
    exfalso
    exact h ⟨(leafIndex, chain, step), value, rfl⟩

attribute [irreducible] keygenChainTargetInput

theorem adaptiveFreshDigestCollisionWith_of_chainCollision
    (secretKey : SecretKey) (initialCache finalCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (forgedValue : Digest) (forgedOutput honestOutput : HashOutput)
    (hforgedFinal : finalCache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step forgedValue) =
        some forgedOutput)
    (hforgedInitial : initialCache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step forgedValue) = none)
    (hhonestInitial : initialCache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
        (Wots.walk (Concrete.CacheView.chainStep initialCache secretKey.parameter leafIndex chain)
          0 step.val (secretKey.chainStart leafIndex chain))) = some honestOutput)
    (hcollision : Concrete.CacheView.digestAt finalCache
        (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step forgedValue) =
      Concrete.CacheView.digestAt finalCache
        (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
          (Wots.walk (Concrete.CacheView.chainStep initialCache secretKey.parameter leafIndex chain)
            0 step.val (secretKey.chainStart leafIndex chain)))) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenChainTargetInput secretKey initialCache) := by
  let forgedInput := Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
    forgedValue
  refine ⟨forgedInput, forgedOutput, honestOutput, hforgedFinal, hforgedInitial, ?_, ?_⟩
  · rw [show forgedInput = Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
      forgedValue by rfl]
    rw [keygenChainTargetInput_chainInput]
    exact hhonestInitial
  · rw [show forgedInput = Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
      forgedValue by rfl]
    rw [keygenChainTargetInput_chainInput]
    exact hcollision

theorem chainCollision_afterKeygen_orientation
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
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (forgedValue : Digest) (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step forgedValue) =
        some forgedOutput)
    (hne : forgedValue ≠ Wots.walk
      (Concrete.CacheView.chainStep execution.2 secretKey.parameter leafIndex chain)
      0 step.val (secretKey.chainStart leafIndex chain))
    (hstepCollision : Concrete.CacheView.chainStep execution.2 secretKey.parameter leafIndex chain
        step.val forgedValue =
      Concrete.CacheView.chainStep execution.2 secretKey.parameter leafIndex chain step.val
        (Wots.walk (Concrete.CacheView.chainStep execution.2 secretKey.parameter leafIndex chain)
          0 step.val (secretKey.chainStart leafIndex chain))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  have hafterCacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hstable := Concrete.precomputedKeygen_chainWalk_eq_of_cache_le keyResult hkeygen'
    execution.2
    hafterCacheLe leafIndex chain step.val (Nat.le_of_lt step.isLt)
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.precomputedKeygen_cache_has_chainInput keyResult hkeygen' leafIndex chain step
  have hforgedInitial := Concrete.precomputedKeygen_cache_chainInput_eq_none_of_ne
    keyResult hkeygen' leafIndex chain step forgedValue (by
      intro heq
      apply hne
      exact heq.trans hstable)
  have hcollision := hstepCollision
  rw [← hstable] at hcollision
  rw [Concrete.CacheView.chainStep_eq _ _ _ _ _ _ step.isLt,
    Concrete.CacheView.chainStep_eq _ _ _ _ _ _ step.isLt] at hcollision
  exact adaptiveFreshDigestCollisionWith_of_chainCollision keyResult.1.2 keyResult.2
    execution.2 leafIndex chain step forgedValue forgedOutput honestOutput hforgedCached
    hforgedInitial hhonestCached hcollision

theorem same_suffix_collision_facts
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (request : SignRequest)
    (signature forgedSignature : Signature) (signedEncoding forgedEncoding : Encoding)
    (position : TargetSum.SuffixPosition signedEncoding)
    (hsignature : signature = Concrete.CacheReplay.signWithEncoding cache secretKey
      request.leafIndex signature.randomness signedEncoding)
    (hsuffix : Wots.IsSuffixCollisionAt
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain)
      signedEncoding forgedEncoding signature.chainValue forgedSignature.chainValue position) :
    let chain := position.1
    let suffixOffset := position.2.val
    let recoveryOffset := (signedEncoding chain).val - (forgedEncoding chain).val +
      suffixOffset
    let targetStep : ChainStep := ⟨(signedEncoding chain).val + suffixOffset, by
      have hoffset : suffixOffset < chainLength - 1 - (signedEncoding chain).val := by
        simpa only [chain, suffixOffset] using position.2.isLt
      omega⟩
    let forgedValue := Wots.walk
      (Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain)
      (forgedEncoding chain).val recoveryOffset (forgedSignature.chainValue chain)
    recoveryOffset < chainLength - 1 - (forgedEncoding chain).val ∧
      forgedValue ≠ Wots.walk
        (Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain)
        0 targetStep.val (secretKey.chainStart request.leafIndex chain) ∧
      Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain
          targetStep.val forgedValue =
        Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain
          targetStep.val
          (Wots.walk
            (Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain)
            0 targetStep.val (secretKey.chainStart request.leafIndex chain)) := by
  dsimp only [Wots.IsSuffixCollisionAt] at hsuffix
  let chain := position.1
  let suffixOffset := position.2.val
  have hle := hsuffix.1
  have hne := hsuffix.2.1
  have heq := hsuffix.2.2
  have hsignedValue := congrArg (fun candidate : Signature => candidate.chainValue chain)
    hsignature
  simp only [Concrete.CacheReplay.signWithEncoding,
    Concrete.CacheReplay.signedChainValues] at hsignedValue
  rw [hsignedValue] at hne heq
  let step := Concrete.CacheView.chainStep cache secretKey.parameter request.leafIndex chain
  change Wots.walk step (signedEncoding chain).val suffixOffset
      (Wots.walk step (forgedEncoding chain).val
        ((signedEncoding chain).val - (forgedEncoding chain).val)
        (forgedSignature.chainValue chain)) ≠
    Wots.walk step (signedEncoding chain).val suffixOffset
      (Wots.signChain step (signedEncoding chain)
        (secretKey.chainStart request.leafIndex chain)) at hne
  change step ((signedEncoding chain).val + suffixOffset)
      (Wots.walk step (signedEncoding chain).val suffixOffset
        (Wots.walk step (forgedEncoding chain).val
          ((signedEncoding chain).val - (forgedEncoding chain).val)
          (forgedSignature.chainValue chain))) =
    step ((signedEncoding chain).val + suffixOffset)
      (Wots.walk step (signedEncoding chain).val suffixOffset
        (Wots.signChain step (signedEncoding chain)
          (secretKey.chainStart request.leafIndex chain))) at heq
  have hleVal : (forgedEncoding chain).val ≤ (signedEncoding chain).val := by
    exact_mod_cast hle
  have hforgedWalk := (Wots.walk_add step (forgedEncoding chain).val
    ((signedEncoding chain).val - (forgedEncoding chain).val) suffixOffset
    (forgedSignature.chainValue chain)).symm
  rw [Nat.add_sub_of_le hleVal] at hforgedWalk
  have hhonestWalk := Wots.walk_signChain_eq_honest step (signedEncoding chain)
    suffixOffset (secretKey.chainStart request.leafIndex chain)
  change _ ∧ _ ∧ _
  constructor
  · have hoffset : suffixOffset < chainLength - 1 - (signedEncoding chain).val := by
      simpa only [chain, suffixOffset] using position.2.isLt
    change (signedEncoding chain).val - (forgedEncoding chain).val + suffixOffset <
      chainLength - 1 - (forgedEncoding chain).val
    omega
  · rw [← hforgedWalk, ← hhonestWalk]
    exact ⟨hne, heq⟩

theorem fresh_suffix_collision_facts
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (forgedSignature : Signature) (encoding : Encoding)
    (position : TargetSum.SuffixPosition encoding)
    (hsuffix : Wots.IsSuffixCollisionAt
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
      encoding encoding
      (fun chain => Wots.signChain
        (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
        (encoding chain) (secretKey.chainStart leafIndex chain))
      forgedSignature.chainValue position) :
    let chain := position.1
    let suffixOffset := position.2.val
    let targetStep : ChainStep := ⟨(encoding chain).val + suffixOffset, by
      have hoffset : suffixOffset < chainLength - 1 - (encoding chain).val := by
        simpa only [chain, suffixOffset] using position.2.isLt
      omega⟩
    let forgedValue := Wots.walk
      (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
      (encoding chain).val suffixOffset (forgedSignature.chainValue chain)
    suffixOffset < chainLength - 1 - (encoding chain).val ∧
      forgedValue ≠ Wots.walk
        (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
        0 targetStep.val (secretKey.chainStart leafIndex chain) ∧
      Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain
          targetStep.val forgedValue =
        Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain
          targetStep.val
          (Wots.walk
            (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
            0 targetStep.val (secretKey.chainStart leafIndex chain)) := by
  let request : SignRequest := ⟨leafIndex, 0⟩
  let signedSignature := Concrete.CacheReplay.signWithEncoding cache secretKey
    leafIndex forgedSignature.randomness encoding
  have hsignature : signedSignature =
      Concrete.CacheReplay.signWithEncoding cache secretKey request.leafIndex
        signedSignature.randomness encoding := by
    rfl
  have hsuffix' : Wots.IsSuffixCollisionAt
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter
        request.leafIndex chain)
      encoding encoding signedSignature.chainValue forgedSignature.chainValue
      position := by
    have hsignedValues : signedSignature.chainValue = fun chain => Wots.signChain
        (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
        (encoding chain) (secretKey.chainStart leafIndex chain) := by
      funext chain
      rfl
    rw [hsignedValues]
    simpa [request] using hsuffix
  simpa [request, signedSignature] using
    same_suffix_collision_facts cache secretKey request signedSignature
      forgedSignature encoding encoding position hsignature hsuffix'

theorem fresh_suffix_witness_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (forgedEncoding : Encoding) (hverified : execution.1.verified = true)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (position : TargetSum.SuffixPosition forgedEncoding)
    (hsuffix : Wots.IsSuffixCollisionAt
      (fun chain => Concrete.CacheView.chainStep execution.2
        execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
      forgedEncoding forgedEncoding
      (fun chain => Wots.signChain
        (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex chain)
        (forgedEncoding chain)
        (execution.1.secretKey.chainStart execution.1.forgery.leafIndex chain))
      execution.1.forgery.signature.chainValue position) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hafter
  have hfacts := fresh_suffix_collision_facts execution.2 execution.1.secretKey
    execution.1.forgery.leafIndex execution.1.forgery.signature forgedEncoding position hsuffix
  dsimp only at hfacts
  obtain ⟨hoffset, hne, hstepCollision⟩ := hfacts
  let chain := position.1
  let suffixOffset := position.2.val
  have htargetStep : (forgedEncoding chain).val + suffixOffset < chainLength - 1 := by
    have := position.2.isLt
    change suffixOffset < chainLength - 1 - (forgedEncoding chain).val at this
    omega
  let targetStep : ChainStep := ⟨(forgedEncoding chain).val + suffixOffset, htargetStep⟩
  let forgedValue := Wots.walk
    (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex chain)
    (forgedEncoding chain).val suffixOffset
    (execution.1.forgery.signature.chainValue chain)
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_chain_query_cached_as adversary execution hgame
      forgedEncoding hverified hforgedDecode chain suffixOffset hoffset
  apply chainCollision_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    execution.1.secretKey hkeys.2 execution.1.forgery.leafIndex chain targetStep forgedValue
    forgedOutput
  · simpa [chain, suffixOffset, targetStep, forgedValue] using hforgedCached
  · simpa [chain, suffixOffset, targetStep, forgedValue] using hne
  · simpa [chain, suffixOffset, targetStep, forgedValue] using hstepCollision

theorem same_suffix_witness_afterKeygen_orientation
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
    (position : TargetSum.SuffixPosition signedEncoding)
    (hsuffix : Wots.IsSuffixCollisionAt
      (fun chain => Concrete.CacheView.chainStep execution.2
        execution.1.secretKey.parameter request.leafIndex chain)
      signedEncoding forgedEncoding signature.chainValue
      execution.1.forgery.signature.chainValue position) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hafter
  have hsignature := CappedLeaf.detailed_execution_returned_signature_eq adversary execution hgame
    request signature signedEncoding hsignedDecode hreturned
  have hfacts := same_suffix_collision_facts execution.2 execution.1.secretKey request
    signature execution.1.forgery.signature signedEncoding forgedEncoding position
    hsignature hsuffix
  dsimp only at hfacts
  obtain ⟨hrecovery, hne, hstepCollision⟩ := hfacts
  let chain := position.1
  let suffixOffset := position.2.val
  let recoveryOffset := (signedEncoding chain).val - (forgedEncoding chain).val +
    suffixOffset
  have htargetStep : (signedEncoding chain).val + suffixOffset < chainLength - 1 := by
    have := position.2.isLt
    change suffixOffset < chainLength - 1 - (signedEncoding chain).val at this
    omega
  let targetStep : ChainStep := ⟨(signedEncoding chain).val + suffixOffset, htargetStep⟩
  have hsuffixParts := hsuffix
  dsimp only [Wots.IsSuffixCollisionAt] at hsuffixParts
  have hencodingLe : (forgedEncoding chain).val ≤ (signedEncoding chain).val := by
    exact_mod_cast hsuffixParts.1
  have hstepValueEq : (forgedEncoding chain).val + recoveryOffset =
      (signedEncoding chain).val + suffixOffset := by
    dsimp only [recoveryOffset]
    omega
  let forgedValue : LeafIndex → Digest := fun candidateLeafIndex => Wots.walk
    (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
      candidateLeafIndex chain)
    (forgedEncoding chain).val recoveryOffset
    (execution.1.forgery.signature.chainValue chain)
  have hdecodeLeafIndex := congrArg (fun candidateLeafIndex => TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
      candidateLeafIndex
      (execution.1.forgery.message, execution.1.forgery.signature.randomness))) hleafIndex
  have hforgedDecode' : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding := hdecodeLeafIndex.symm.trans hforgedDecode
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_chain_query_cached_as adversary execution hgame
      forgedEncoding hverified hforgedDecode' chain recoveryOffset hrecovery
  have hqueriedStep : (forgedEncoding chain).val + recoveryOffset < chainLength - 1 := by
    omega
  have hstepEq :
      (⟨(forgedEncoding chain).val + recoveryOffset, hqueriedStep⟩ : ChainStep) =
        targetStep := by
    apply Fin.ext
    exact hstepValueEq
  rw [hstepEq] at hforgedCached
  rw [hleafIndex] at hne hstepCollision
  apply chainCollision_afterKeygen_orientation adversary keyResult hkeygen execution
    hafter execution.1.secretKey hkeys.2 execution.1.forgery.leafIndex chain
      targetStep (forgedValue execution.1.forgery.leafIndex) forgedOutput
  · simpa [chain, recoveryOffset, targetStep, forgedValue] using hforgedCached
  · simpa [chain, suffixOffset, recoveryOffset, targetStep, forgedValue] using hne
  · simpa [chain, suffixOffset, recoveryOffset, targetStep, forgedValue] using
      hstepCollision

theorem suffixCollision_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (slot : Fin verificationChainHashes)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.suffixCollision slot)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hbad⟩ := hsame
    change ∃ position : TargetSum.SuffixPosition signedEncoding,
      TargetSum.enumerateSuffixPositions signedEncoding
        (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 position = slot ∧
      Wots.IsSuffixCollisionAt
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.leafIndex chain)
        signedEncoding forgedEncoding signature.chainValue
        execution.1.forgery.signature.chainValue position at hbad
    obtain ⟨position, _hslot, hsuffix⟩ := hbad
    exact same_suffix_witness_afterKeygen_orientation adversary keyResult hkeygen
      execution hafter hevent.1 request signature signedEncoding forgedEncoding
      hsignedDecode hforgedDecode hreturned hleafIndex position hsuffix
  · obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hbad⟩ := hfresh
    change ∃ position : TargetSum.SuffixPosition forgedEncoding,
      TargetSum.enumerateSuffixPositions forgedEncoding hforgedValid position = slot ∧
      Wots.IsSuffixCollisionAt
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
        forgedEncoding forgedEncoding
        (fun chain => Wots.signChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex chain)
          (forgedEncoding chain)
          (execution.1.secretKey.chainStart execution.1.forgery.leafIndex chain))
        execution.1.forgery.signature.chainValue position at hbad
    obtain ⟨position, _hslot, hsuffix⟩ := hbad
    exact fresh_suffix_witness_afterKeygen_orientation adversary keyResult hkeygen
      execution hafter forgedEncoding hevent.1 hforgedDecode position hsuffix

end XmssSecurity.CappedSuffix
