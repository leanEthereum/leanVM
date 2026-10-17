import XmssSecurity.Proof.EncodingTargetMap
import XmssSecurity.Proof.SigningCacheTrace
import XmssSecurity.Proof.WinningEventReduction

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- A winning encoding event identifies a genuine returned signature and a distinct forged encoding input with the same cached 128-bit digest. Its transcript contains at most one request per leaf index. -/
theorem winning_encoding_event_has_signed_collision
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    SigningTranscript.Valid outcome.signingLog ∧
    outcome.signingLog.length ≤ lifetime ∧
    ∃ request signature signedOutput forgedOutput,
      SigningTranscript.Returned outcome.signingLog request signature ∧
      request.leafIndex = outcome.forgery.leafIndex ∧
      Concrete.CacheView.encodingInput outcome.secretKey.parameter request.leafIndex
          (request.message, signature.randomness) ≠
        Concrete.CacheView.encodingInput outcome.secretKey.parameter request.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      cache (Concrete.CacheView.encodingInput outcome.secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some signedOutput ∧
      cache (Concrete.CacheView.encodingInput outcome.secretKey.parameter request.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some forgedOutput ∧
      truncateHash signedOutput = truncateHash forgedOutput := by
  refine ⟨hevent.signingTranscript_valid,
    hevent.signingLog_length_le_lifetime, ?_⟩
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hencoding⟩ := hsame
    change (request.message, signature.randomness) ≠
        (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.leafIndex
          (request.message, signature.randomness) =
        Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness) at hencoding
    obtain ⟨signedOutput, hsignedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.leafIndex request.message signature.randomness
        signedEncoding hsignedDecode
    obtain ⟨forgedOutput, hforgedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.leafIndex outcome.forgery.message
        outcome.forgery.signature.randomness forgedEncoding hforgedDecode
    refine ⟨request, signature, signedOutput, forgedOutput, hreturned, hleafIndex, ?_,
      hsignedCached, hforgedCached, ?_⟩
    · intro hinput
      exact hencoding.1
        (Concrete.CacheView.encodingInput_injective outcome.secretKey.parameter request.leafIndex
          hinput)
    · rw [Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hsignedCached,
        Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedCached] at hencoding
      exact hencoding.2
  · simp [Concrete.FreshLeafIndexBadEventOccurs,
      XmssSecurity.FreshLeafIndexBadEventOccurs] at hfresh

/-- A winning encoding collision is oriented at the matching signing boundary: either the forged encoding input was already cached before signing, or it was still fresh when the signer installed the honest target. -/
theorem winning_encoding_event_trace_temporal_decomposition
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (trace : SigningCacheTrace)
    (hlog : trace.toSigningLog = outcome.signingLog)
    (hcaches : trace.CachesLe cache)
    (hcached : trace.SuccessfulEncodingsCached outcome.secretKey)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ entry ∈ trace,
      entry.PreexistingEncodingCollision outcome.secretKey ∨
        entry.FreshForgedEncodingCollision outcome.secretKey outcome.forgery cache := by
  obtain ⟨_hvalid, _hlength, request, signature, signedOutput, forgedOutput,
    hreturned, hleafIndex, hne, hsigned, hforged, hdigest⟩ :=
    winning_encoding_event_has_signed_collision cache outcome hevent
  have hreturnedTrace :
      SigningTranscript.Returned trace.toSigningLog request signature := by
    rw [hlog]
    exact hreturned
  obtain ⟨entry, hentry, hrequest, hsignature⟩ :=
    (SigningTranscript.returned_toSigningLog_iff trace request signature).mp
      hreturnedTrace
  subst request
  obtain ⟨localSignedOutput, hlocalSigned⟩ :=
    hcached entry hentry signature hsignature
  have hlocalFinal := (hcaches entry hentry).2 hlocalSigned
  have houtput : localSignedOutput = signedOutput :=
    Option.some.inj (hlocalFinal.symm.trans hsigned)
  subst localSignedOutput
  let forgedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
    outcome.forgery.leafIndex
      (outcome.forgery.message, outcome.forgery.signature.randomness)
  have hforgedFinal : cache forgedInput = some forgedOutput := by
    dsimp [forgedInput]
    rw [← hleafIndex]
    exact hforged
  have hdistinct :
      Concrete.CacheView.encodingInput outcome.secretKey.parameter entry.request.leafIndex
          (entry.request.message, signature.randomness) ≠ forgedInput := by
    dsimp [forgedInput]
    rw [← hleafIndex]
    exact hne
  cases hinitial : entry.initialCache forgedInput with
  | none =>
      refine ⟨entry, hentry, Or.inr ?_⟩
      refine ⟨signature, signedOutput, forgedOutput, hsignature, hleafIndex,
        hinitial, hlocalSigned, hforgedFinal, hdistinct, hdigest⟩
  | some oldOutput =>
      have holdFinal := (hcaches entry hentry).1 hinitial
      have holdOutput : oldOutput = forgedOutput :=
        Option.some.inj (holdFinal.symm.trans hforgedFinal)
      subst oldOutput
      refine ⟨entry, hentry, Or.inl ?_⟩
      refine ⟨signature, signedOutput,
        (outcome.forgery.message, outcome.forgery.signature.randomness),
        forgedOutput, hsignature, hlocalSigned, ?_, ?_, hdigest⟩
      · rw [hleafIndex]
        exact hinitial
      · intro heq
        apply hdistinct
        dsimp [forgedInput]
        rw [← hleafIndex]
        exact congrArg
          (Concrete.CacheView.encodingInput outcome.secretKey.parameter
            entry.request.leafIndex) heq.symm

/-- A winning encoding event is a cached selection with a colliding input, a fresh selection landing on an older digest, or a fresh selection hit by a later digest. -/
theorem winning_encoding_event_trace_monitor_decomposition
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (trace : SigningCacheTrace)
    (hlog : trace.toSigningLog = outcome.signingLog)
    (hcaches : trace.CachesLe cache)
    (hcached : trace.SuccessfulEncodingsCached outcome.secretKey)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ entry ∈ trace,
      entry.CachedSelectionCollision outcome.secretKey cache ∨
        entry.FreshSigningEncodingCollision outcome.secretKey ∨
          (entry.FreshForgedEncodingCollision outcome.secretKey outcome.forgery cache ∧
            ∃ signature, entry.signature = some signature ∧
              entry.initialCache
                (Concrete.CacheView.encodingInput outcome.secretKey.parameter
                  entry.request.leafIndex (entry.request.message, signature.randomness)) = none) := by
  obtain ⟨entry, hentry, hpreexisting | hfresh⟩ :=
    winning_encoding_event_trace_temporal_decomposition cache outcome trace
      hlog hcaches hcached hevent
  · obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
      hsigned, hold, hne, hdigest⟩ := hpreexisting
    cases hinitial : entry.initialCache
        (Concrete.CacheView.encodingInput outcome.secretKey.parameter entry.request.leafIndex
          (entry.request.message, signature.randomness)) with
    | none =>
        exact ⟨entry, hentry, Or.inr (Or.inl ⟨signature, signedOutput, oldInput, oldOutput,
          hsignature, hinitial, hsigned, hold, hne, hdigest⟩)⟩
    | some output =>
        have houtput : output = signedOutput := Option.some.inj
          (((hcaches entry hentry).1 hinitial).symm.trans ((hcaches entry hentry).2 hsigned))
        subst output
        exact ⟨entry, hentry, Or.inl ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
          hinitial, (hcaches entry hentry).1 hold, hne, hdigest⟩⟩
  · obtain ⟨signature, signedOutput, forgedOutput, hsignature, hleafIndex, hforgedInitial,
      hsigned, hforged, hdistinct, hdigest⟩ := hfresh
    cases hinitial : entry.initialCache
        (Concrete.CacheView.encodingInput outcome.secretKey.parameter entry.request.leafIndex
          (entry.request.message, signature.randomness)) with
    | none =>
        exact ⟨entry, hentry, Or.inr (Or.inr ⟨⟨signature, signedOutput, forgedOutput, hsignature,
          hleafIndex, hforgedInitial, hsigned, hforged, hdistinct, hdigest⟩,
          signature, hsignature, hinitial⟩)⟩
    | some output =>
        have houtput : output = signedOutput := Option.some.inj
          (((hcaches entry hentry).1 hinitial).symm.trans ((hcaches entry hentry).2 hsigned))
        subst output
        refine ⟨entry, hentry, Or.inl ⟨signature, signedOutput,
          (outcome.forgery.message, outcome.forgery.signature.randomness), forgedOutput,
          hsignature, hinitial, ?_, ?_, hdigest⟩⟩
        · rw [hleafIndex]
          exact hforged
        · intro heq
          apply hdistinct
          rw [← hleafIndex, ← heq]

end XmssSecurity
