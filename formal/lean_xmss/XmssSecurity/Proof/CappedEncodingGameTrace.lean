import XmssSecurity.Proof.CappedEncodingMonitor
import XmssSecurity.Proof.CappedSigningCacheTrace

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def cappedEncodingTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
        ProbComp) :=
  QueryImpl.extendState
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey)

theorem cappedEncodingTracedMappedAdversaryImpl_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (initialTrace : EncodingActionTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState := by
  exact OracleComp.extendState_run_proj_eq
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey) computation initialState initialTrace

noncomputable def cappedDetailedGameAfterKeygenWithEncodingTrace
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let (forgery, adversaryState, encodingTrace) ←
    (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((initialCache, []), [])
  let (verified, finalCache) ←
    (simulateQ romImpl
      (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
        forgery.signature)).run adversaryState.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey forgery
    adversaryState.1 finalCache encodingTrace
  pure (⟨publicKey, secretKey, forgery, adversaryState.2.toSigningLog, verified⟩,
    ((finalCache, adversaryState.2), finalEncodingTrace))

theorem cappedDetailedGameAfterKeygenWithEncodingTrace_projection
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result => (result.1, result.2.1)) <$>
        cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
          initialCache =
      cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
        initialCache := by
  let finishEncoding : Forgery ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) →
      ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) :=
    fun result => do
      let (verified, finalCache) ←
        (simulateQ romImpl
          (Concrete.scheme.verify publicKey result.1.leafIndex result.1.message
            result.1.signature)).run result.2.1.1
      pure (⟨publicKey, secretKey, result.1, result.2.1.2.toSigningLog, verified⟩,
        (finalCache, result.2.1.2))
  let finishSigning : Forgery × (QueryCache HashSpec × SigningCacheTrace) →
      ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) :=
    fun result => do
      let (verified, finalCache) ←
        (simulateQ romImpl
          (Concrete.scheme.verify publicKey result.1.leafIndex result.1.message
            result.1.signature)).run result.2.1
      pure (⟨publicKey, secretKey, result.1, result.2.2.toSigningLog, verified⟩,
        (finalCache, result.2.2))
  have hbridge := congrArg (fun computation => computation >>= finishSigning)
    (cappedEncodingTracedMappedAdversaryImpl_projection publicKey secretKey
      (adversary.main publicKey) (initialCache, []) [])
  simpa [cappedDetailedGameAfterKeygenWithEncodingTrace,
    cappedDetailedGameAfterKeygenWithSigningTrace, finishEncoding, finishSigning,
    bind_map_left, map_bind, bind_assoc, Prod.map] using hbridge

noncomputable def cappedDetailedGameWithEncodingTrace
    (adversary : Adversary) :
    ProbComp (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let keyResult ← (simulateQ romImpl Concrete.scheme.keygen).run ∅
  cappedDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
    keyResult.1.2 keyResult.2

theorem cappedDetailedGameWithEncodingTrace_projection
    (adversary : Adversary) :
    (fun result => (result.1, result.2.1)) <$>
        cappedDetailedGameWithEncodingTrace adversary =
      cappedDetailedGameWithSigningTrace adversary := by
  unfold cappedDetailedGameWithEncodingTrace cappedDetailedGameWithSigningTrace
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  exact cappedDetailedGameAfterKeygenWithEncodingTrace_projection adversary
    keyResult.1.1 keyResult.1.2 keyResult.2

theorem cappedDetailedGameWithEncodingTrace_cache_projection
    (adversary : Adversary) :
    (fun result => (result.1, result.2.1.1)) <$>
        cappedDetailedGameWithEncodingTrace adversary =
      detailedGameWithCache Concrete.scheme adversary := by
  calc
    _ = Prod.map id Prod.fst <$>
        cappedDetailedGameWithSigningTrace adversary := by
          rw [← cappedDetailedGameWithEncodingTrace_projection, Functor.map_map]
          rfl
    _ = _ := cappedDetailedGameWithSigningTrace_cache_projection adversary

end XmssSecurity
