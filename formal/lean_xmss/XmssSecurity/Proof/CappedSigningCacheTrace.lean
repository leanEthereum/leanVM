module

public import XmssSecurity.Proof.CappedSigningLogReplay
public import XmssSecurity.Proof.PrecomputedBoundedSignCache
public import XmssSecurity.Proof.SigningCacheTrace
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import all PolyFun.PFunctor.Handler.Instrumentation

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def SigningCacheEntry.PreservesOtherValidEncodingInputs
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∀ signature, entry.signature = some signature →
    ∀ targetLeafIndex targetInput encoding,
      TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash entry.finalCache secretKey.parameter
            targetLeafIndex targetInput) = some encoding →
      Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
          (entry.request.message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput →
      entry.initialCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none →
      entry.finalCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) = none

def SigningCacheTrace.PreservesOtherValidEncodingInputs
    (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, entry.PreservesOtherValidEncodingInputs secretKey

noncomputable def cappedUnloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  intro input
  cases input with
  | inl worldInput => exact romImpl worldInput
  | inr request =>
      exact simulateQ romImpl
        (Concrete.scheme.sign secretKey request.leafIndex request.message)

noncomputable def cappedCacheTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp) :=
  QueryImpl.extendState (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate

theorem cappedUnloggedMappedAdversaryImpl_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hmem : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          change result ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
          rw [hrun, support_map] at hmem
          obtain ⟨sample, _hsample, heq⟩ := hmem
          exact le_of_eq (congrArg Prod.snd heq)
      | inr hashInput =>
          change result ∈ support
            ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
          exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache
            result hmem
  | inr request =>
      exact xmssRom_cache_le
        (Concrete.scheme.sign secretKey request.leafIndex request.message)
        initialCache result hmem

theorem cappedCacheTracedMappedAdversaryImpl_query_cachesLe
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact signingCacheTraceUpdate_cachesLe input initialCache output finalCache
    initialTrace htrace
    (cappedUnloggedMappedAdversaryImpl_cache_le publicKey secretKey input initialCache
      (output, finalCache) hbase)

theorem cappedCacheTracedMappedAdversaryImpl_query_successfulEncodingsCached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SuccessfulEncodingsCached secretKey)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.SuccessfulEncodingsCached secretKey := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput => simpa [signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature
        change output = some signature at hsignature
        subst output
        exact Concrete.precomputedCappedSign_success_encodingInput_cached secretKey request
          initialCache finalCache signature hbase

theorem cappedCacheTracedMappedAdversaryImpl_query_preservesOtherValidEncodingInputs
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.PreservesOtherValidEncodingInputs secretKey)
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.PreservesOtherValidEncodingInputs secretKey := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput => simpa [SigningCacheTrace.PreservesOtherValidEncodingInputs,
      signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature targetLeafIndex targetInput encoding hdecode hother hnone
        change output = some signature at hsignature
        subst output
        by_cases hleafIndex : request.leafIndex = targetLeafIndex
        · exact Concrete.precomputedCappedSign_preserves_later_valid_other_encodingInput
            secretKey request.leafIndex targetLeafIndex request.message targetInput
            initialCache finalCache finalCache (some signature) hbase le_rfl encoding hdecode
            (by
              intro candidate hcand
              have heq : candidate = signature := Option.some.inj hcand.symm
              subst candidate
              exact hother)
            hnone rfl
        · exact Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput
            secretKey request.leafIndex targetLeafIndex request.message targetInput
            initialCache finalCache (some signature) hbase hleafIndex hnone

theorem cappedCacheTracedMappedAdversaryImpl_cachesLe
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.2.CachesLe state.1)
    (by
      intro input state hstate queryResult hquery
      exact cappedCacheTracedMappedAdversaryImpl_query_cachesLe
        publicKey secretKey input state.1 state.2 queryResult hstate hquery)
    computation (initialCache, initialTrace) htrace result hmem

theorem cappedCacheTracedMappedAdversaryImpl_successfulEncodingsCached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SuccessfulEncodingsCached secretKey)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.SuccessfulEncodingsCached secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.2.SuccessfulEncodingsCached secretKey)
    (by
      intro input state hstate queryResult hquery
      exact cappedCacheTracedMappedAdversaryImpl_query_successfulEncodingsCached
        publicKey secretKey input state.1 state.2 queryResult hstate hquery)
    computation (initialCache, initialTrace) htrace result hmem

theorem cappedCacheTracedMappedAdversaryImpl_preservesOtherValidEncodingInputs
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.PreservesOtherValidEncodingInputs secretKey)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.PreservesOtherValidEncodingInputs secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.2.PreservesOtherValidEncodingInputs secretKey)
    (by
      intro input state hstate queryResult hquery
      exact
        cappedCacheTracedMappedAdversaryImpl_query_preservesOtherValidEncodingInputs
          publicKey secretKey input state.1 state.2 queryResult hstate hquery)
    computation (initialCache, initialTrace) htrace result hmem

noncomputable def cappedSelectivelyLoggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  QueryImpl.withTraceAppend (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
    signingLogFragment

noncomputable def cappedLogTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × QueryLog SigningSpec) ProbComp) :=
  QueryImpl.extendState (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
    signingLogUpdate

theorem cappedSelectivelyLoggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest) :
    cappedSelectivelyLoggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      QueryImpl.withLogging
        (fun request => simulateQ romImpl
          (Concrete.scheme.sign secretKey
            request.leafIndex request.message)) request := by
  rfl

theorem cappedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest) :
    cappedMappedAdversaryImpl publicKey secretKey (.inr request) =
      QueryImpl.withLogging
        (fun request => simulateQ romImpl
          (Concrete.scheme.sign secretKey
            request.leafIndex request.message)) request := by
  change WriterT.mk (simulateQ romImpl
      ((QueryImpl.withLogging (spec := SigningSpec)
        (fun request => Concrete.scheme.sign secretKey
          request.leafIndex request.message) request).run)) = _
  apply WriterT.ext
  rw [WriterT.run_mk, QueryImpl.run_withLogging_apply,
    QueryImpl.run_withLogging_apply, simulateQ_bind]
  simp

theorem cappedSelectivelyLoggedMappedAdversaryImpl_eq_mapped
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedSelectivelyLoggedMappedAdversaryImpl publicKey secretKey =
      cappedMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      change (do
          let output ← liftM (romImpl worldInput)
          tell ([] : QueryLog SigningSpec)
          pure output) =
        WriterT.mk ((fun output => (output, ([] : QueryLog SigningSpec))) <$>
          romImpl worldInput)
      apply WriterT.ext
      simp
  | inr request =>
      rw [cappedSelectivelyLoggedMappedAdversaryImpl_apply_inr,
        cappedMappedAdversaryImpl_apply_inr]

theorem cappedCacheTracedMappedAdversaryImpl_cache_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run initialCache := by
  exact OracleComp.extendState_run_proj_eq
    (cappedUnloggedMappedAdversaryImpl publicKey secretKey) signingCacheTraceUpdate
    computation initialCache initialTrace

theorem cappedCacheTracedMappedAdversaryImpl_log_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$>
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (cappedLogTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace.toSigningLog) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (cappedLogTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => (state.1, state.2.toSigningLog))
  intro input state
  rw [cappedCacheTracedMappedAdversaryImpl, cappedLogTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, QueryImpl.extendState_apply, map_bind]
  apply bind_congr
  intro result
  simp only [map_pure]
  simpa [Prod.map] using congrArg (fun log => (result.1, (result.2, log)))
    (signingCacheTraceUpdate_toSigningLog input state.1 result.1 result.2 state.2)

theorem cappedSelectivelyLoggedMappedAdversaryImpl_query_run_eq_logTraced
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialLog : QueryLog SigningSpec) :
    (fun result =>
      (result.1.1, (result.2, initialLog ++ result.1.2))) <$>
        (((cappedSelectivelyLoggedMappedAdversaryImpl publicKey secretKey input).run).run
          initialCache) =
      (cappedLogTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialLog) := by
  rw [cappedSelectivelyLoggedMappedAdversaryImpl, QueryImpl.withTraceAppend_apply,
    cappedLogTracedMappedAdversaryImpl, QueryImpl.extendState_apply]
  simp only [WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
    WriterT.run_pure', StateT.run_bind, StateT.run_pure, map_bind,
    bind_map_left, pure_bind, map_pure, Prod.map, id_eq]
  apply bind_congr
  intro result
  simp [signingLogUpdate]

theorem cappedSelectivelyLoggedMappedAdversaryImpl_run_eq_logTraced
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialLog : QueryLog SigningSpec) :
    (fun result =>
      (result.1.1, (result.2, initialLog ++ result.1.2))) <$>
        (((simulateQ (cappedSelectivelyLoggedMappedAdversaryImpl publicKey secretKey)
          computation).run).run initialCache) =
      (simulateQ (cappedLogTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialLog) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialLog with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, WriterT.run_bind', StateT.run_bind, map_bind, id_map]
      rw [← cappedSelectivelyLoggedMappedAdversaryImpl_query_run_eq_logTraced
        publicKey secretKey input initialCache initialLog]
      simp only [bind_map_left]
      apply bind_congr
      intro prefixResult
      simpa [List.append_assoc] using
        ih prefixResult.1.1 prefixResult.2 (initialLog ++ prefixResult.1.2)

theorem cappedCacheTracedMappedAdversaryImpl_log_projection_eq_mapped
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) :
    Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$>
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, []) =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey)
          computation).run).run initialCache) := by
  rw [cappedCacheTracedMappedAdversaryImpl_log_projection]
  simp only [SigningCacheTrace.toSigningLog, List.map_nil]
  rw [← cappedSelectivelyLoggedMappedAdversaryImpl_run_eq_logTraced
    publicKey secretKey computation initialCache []]
  rw [cappedSelectivelyLoggedMappedAdversaryImpl_eq_mapped]
  rfl

noncomputable def cappedDetailedGameAfterKeygenWithSigningTrace
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) := do
  let (forgery, adversaryCache, trace) ←
    (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let (verified, finalCache) ←
    (simulateQ romImpl
      (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
        forgery.signature)).run adversaryCache
  pure (⟨publicKey, secretKey, forgery, trace.toSigningLog, verified⟩,
    (finalCache, trace))

theorem cappedDetailedGameAfterKeygenWithSigningTrace_cache_projection
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    Prod.map id Prod.fst <$>
        cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
          initialCache =
      (simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey)).run
          initialCache := by
  let finish : Forgery × (QueryCache HashSpec × QueryLog SigningSpec) →
      ProbComp (GameOutcome × QueryCache HashSpec) := fun result => do
    let (verified, finalCache) ←
      (simulateQ romImpl
        (Concrete.scheme.verify publicKey result.1.leafIndex result.1.message
          result.1.signature)).run result.2.1
    pure (⟨publicKey, secretKey, result.1, result.2.2, verified⟩, finalCache)
  have hbridge := congrArg (fun computation => computation >>= finish)
    (cappedCacheTracedMappedAdversaryImpl_log_projection_eq_mapped publicKey secretKey
      (adversary.main publicKey) initialCache)
  simpa [cappedDetailedGameAfterKeygenWithSigningTrace, detailedGameAfterKeygen,
    cappedMappedAdversaryImpl, finish, bind_map_left, map_bind, bind_assoc,
    Prod.map, QueryImpl.simulateQ_writerTMapBase_run] using hbridge

noncomputable def cappedDetailedGameWithSigningTrace
    (adversary : Adversary) :
    ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) := do
  let keyResult ← (simulateQ romImpl Concrete.scheme.keygen).run ∅
  cappedDetailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1 keyResult.1.2
    keyResult.2

theorem cappedDetailedGameWithSigningTrace_cache_projection
    (adversary : Adversary) :
    Prod.map id Prod.fst <$> cappedDetailedGameWithSigningTrace adversary =
      detailedGameWithCache Concrete.scheme adversary := by
  unfold cappedDetailedGameWithSigningTrace detailedGameWithCache detailedGameCore
  rw [simulateQ_bind, StateT.run_bind]
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  exact cappedDetailedGameAfterKeygenWithSigningTrace_cache_projection adversary
    keyResult.1.1 keyResult.1.2 keyResult.2

theorem cappedDetailedGameAfterKeygenWithSigningTrace_invariants
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
        initialCache)) :
    result.1.secretKey = secretKey ∧
      result.2.2.toSigningLog = result.1.signingLog ∧
      result.2.2.CachesLe result.2.1 ∧
      result.2.2.SuccessfulEncodingsCached secretKey := by
  unfold cappedDetailedGameAfterKeygenWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have htrace := cappedCacheTracedMappedAdversaryImpl_cachesLe publicKey secretKey
      (adversary.main publicKey) initialCache []
      (forgery, (adversaryCache, trace)) (by simp [SigningCacheTrace.CachesLe])
      hadversary
    exact htrace.mono (xmssRom_cache_le
      (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
        forgery.signature) adversaryCache (verified, finalCache) hverify)
  · exact cappedCacheTracedMappedAdversaryImpl_successfulEncodingsCached
      publicKey secretKey (adversary.main publicKey) initialCache []
      (forgery, (adversaryCache, trace))
      (by simp [SigningCacheTrace.SuccessfulEncodingsCached]) hadversary

theorem cappedDetailedGameAfterKeygenWithSigningTrace_preservesOtherValidEncodingInputs
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
        initialCache)) :
    result.2.2.PreservesOtherValidEncodingInputs secretKey := by
  unfold cappedDetailedGameAfterKeygenWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cappedCacheTracedMappedAdversaryImpl_preservesOtherValidEncodingInputs
    publicKey secretKey (adversary.main publicKey) initialCache []
    (forgery, (adversaryCache, trace))
    (by simp [SigningCacheTrace.PreservesOtherValidEncodingInputs]) hadversary

theorem cappedDetailedGameWithSigningTrace_invariants
    (adversary : Adversary)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (cappedDetailedGameWithSigningTrace adversary)) :
    result.2.2.toSigningLog = result.1.signingLog ∧
      result.2.2.CachesLe result.2.1 ∧
      result.2.2.SuccessfulEncodingsCached result.1.secretKey := by
  unfold cappedDetailedGameWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  obtain ⟨hsecretKey, hlog, hcaches, hcached⟩ :=
    cappedDetailedGameAfterKeygenWithSigningTrace_invariants adversary
      publicKey secretKey keyCache result hrest
  exact ⟨hlog, hcaches, by simpa [hsecretKey] using hcached⟩

theorem cappedDetailedGameWithSigningTrace_preservesOtherValidEncodingInputs
    (adversary : Adversary)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (cappedDetailedGameWithSigningTrace adversary)) :
    result.2.2.PreservesOtherValidEncodingInputs result.1.secretKey := by
  unfold cappedDetailedGameWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  have hpreserves :=
    cappedDetailedGameAfterKeygenWithSigningTrace_preservesOtherValidEncodingInputs
      adversary publicKey secretKey keyCache result hrest
  have hsecretKey :=
    (cappedDetailedGameAfterKeygenWithSigningTrace_invariants adversary publicKey
      secretKey keyCache result hrest).1
  simpa [hsecretKey] using hpreserves

theorem SigningCacheEntry.freshForgedEncodingCollision_finalCache_none_of_valid
    (secretKey : SecretKey) (forgery : Forgery)
    (gameCache : QueryCache HashSpec) (entry : SigningCacheEntry)
    (hpreserves : entry.PreservesOtherValidEncodingInputs secretKey)
    (hcache : entry.finalCache ≤ gameCache)
    (hevent : entry.FreshForgedEncodingCollision secretKey forgery gameCache)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash gameCache secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = some encoding) :
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = none := by
  obtain ⟨signature, _signedOutput, forgedOutput, hsignature, _hleafIndex,
    hinitial, _hsigned, hforged, hne, _hdigest⟩ := hevent
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter
    forgery.leafIndex (forgery.message, forgery.signature.randomness)
  cases hlocal : entry.finalCache forgedInput with
  | none => rfl
  | some localOutput =>
      have hgame := hcache hlocal
      have houtput : localOutput = forgedOutput :=
        Option.some.inj (hgame.symm.trans hforged)
      have hdecodeLocal : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash entry.finalCache secretKey.parameter
            forgery.leafIndex (forgery.message, forgery.signature.randomness)) =
          some encoding := by
        rw [Concrete.CacheView.encodingHash,
          Concrete.CacheView.digestAt_eq_of_cache_eq_some hlocal, houtput,
          ← Concrete.CacheView.digestAt_eq_of_cache_eq_some hforged,
          ← Concrete.CacheView.encodingHash]
        exact hdecode
      have hnone := hpreserves signature hsignature forgery.leafIndex
        (forgery.message, forgery.signature.randomness) encoding hdecodeLocal hne
        hinitial
      rw [hlocal] at hnone
      exact hnone

theorem SigningCacheEntry.postSigningFreshForgedEncodingCollision_of_valid_fresh
    (secretKey : SecretKey) (forgery : Forgery)
    (gameCache : QueryCache HashSpec) (entry : SigningCacheEntry)
    (hpreserves : entry.PreservesOtherValidEncodingInputs secretKey)
    (hcache : entry.finalCache ≤ gameCache)
    (hevent : entry.FreshForgedEncodingCollision secretKey forgery gameCache)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash gameCache secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = some encoding)
    (signature : Signature) (hsignature : entry.signature = some signature)
    (hsignedFresh : entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = none) :
    entry.PostSigningFreshForgedEncodingCollision secretKey forgery gameCache :=
  ⟨hevent, entry.freshForgedEncodingCollision_finalCache_none_of_valid secretKey
    forgery gameCache hpreserves hcache hevent encoding hdecode,
    signature, hsignature, hsignedFresh⟩

end XmssSecurity
