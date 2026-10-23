import XmssSecurity.Proof.CappedExactFirstLane
import XmssSecurity.Proof.CappedGlobalFirstLaneExperiment
import XmssSecurity.Proof.StateLens
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

abbrev SourceSigningTracedState :=
  (QueryCache HashSpec × SigningCacheTrace) × AttackerActionTrace

def sourceSigningTracedStateProjection
    (state : SourceSigningTracedState) : SourceTracedState :=
  (state.1.1, state.2)

noncomputable def sourceSigningTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SourceSigningTracedState ProbComp) :=
  actionTracedStateImpl
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    attackerActionFragment

def sourceSigningTracedQueryResult
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState) :
    (OracleWorld + SigningSpec).Range input × SourceSigningTracedState :=
  (result.1,
    ((result.2.1,
      signingCacheTraceUpdate input initialState.1.1 result.1 result.2.1
        initialState.1.2), result.2.2))

theorem sourceSigningTracedMappedAdversaryImpl_query_eq_map
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState) :
    (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState =
      sourceSigningTracedQueryResult input initialState <$>
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
          (sourceSigningTracedStateProjection initialState) := by
  unfold sourceSigningTracedMappedAdversaryImpl actionTracedStateImpl
    sourceSigningTracedQueryResult sourceSigningTracedStateProjection
  unfold cappedCacheTracedMappedAdversaryImpl QueryImpl.extendState
  rw [cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl]
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
  simp only [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro result
  rfl

theorem sourceSigningTracedMappedAdversaryImpl_query_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState) :
    (fun result => (result.1,
        sourceSigningTracedStateProjection result.2)) <$>
        (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
          initialState =
      (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        (sourceSigningTracedStateProjection initialState) := by
  rw [sourceSigningTracedMappedAdversaryImpl_query_eq_map]
  simp [Functor.map_map, sourceSigningTracedQueryResult,
    sourceSigningTracedStateProjection]

def GlobalSigningMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState) : Prop :=
  GlobalMonitoredTracedStateRelation left right
    (sourceSigningTracedStateProjection leftState) rightState

theorem relTriple_programmed_globalHighMonitored_signingAction
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      leftState rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceSigningTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨
          rightResult.2.1.bad right.1.2) := by
  let enrich := sourceSigningTracedQueryResult input leftState
  let project := sourceSigningTracedStateProjection leftState
  have hbase := relTriple_programmed_globalHighMonitored_action left right hrel
    hleftSupport hrightSupport project rightState hstate input
  have hlifted : RelTriple
      (enrich <$> (sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run project)
      (id <$> (globalHighMonitoredMappedAdversaryImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨
          rightResult.2.1.bad right.1.2) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2⟩
    · exact Or.inr hbad
  rw [id_map] at hlifted
  rw [sourceSigningTracedMappedAdversaryImpl_query_eq_map]
  exact hlifted

noncomputable def sourceSigningTracedVerifierImpl :
    QueryImpl OracleWorld (StateT SourceSigningTracedState ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, ((result.2.1, state.1.2), result.2.2))) <$>
      (sourceDirectTracedVerifierImpl input).run
        (sourceSigningTracedStateProjection state)

theorem sourceSigningTracedVerifierImpl_query_run_eq
    (input : OracleWorld.Domain) (initialState : SourceSigningTracedState) :
    (sourceSigningTracedVerifierImpl input).run initialState =
      (fun result =>
        (result.1, ((result.2, initialState.1.2), initialState.2))) <$>
        (romImpl input).run initialState.1.1 := by
  unfold sourceSigningTracedVerifierImpl
  rw [StateT.run_mk, sourceDirectTracedVerifierImpl_query_run_eq]
  simp [Functor.map_map, sourceSigningTracedStateProjection]

theorem sourceSigningTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceSigningTracedState) :
    (simulateQ sourceSigningTracedVerifierImpl computation).run initialState =
      (fun result =>
        (result.1, ((result.2, initialState.1.2), initialState.2))) <$>
        (simulateQ romImpl computation).run initialState.1.1 := by
  let lens : StateLens SourceSigningTracedState (QueryCache HashSpec) :=
    ⟨fun state => state.1.1,
      fun state nextCache => ((nextCache, state.1.2), state.2),
      by intro state; rcases state with ⟨⟨cache, signingTrace⟩, actionTrace⟩; rfl,
      by simp, by simp⟩
  exact lens.simulateQ_run_eq sourceSigningTracedVerifierImpl romImpl
    sourceSigningTracedVerifierImpl_query_run_eq computation initialState

theorem relTriple_programmed_globalHighMonitored_signingVerifierQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      leftState rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceSigningTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨
          rightResult.2.1.bad right.1.2) := by
  let project := sourceSigningTracedStateProjection leftState
  let enrich := fun result : OracleWorld.Range input × SourceTracedState =>
    (result.1, ((result.2.1, leftState.1.2), result.2.2))
  have hbase := relTriple_programmed_globalHighMonitored_verifier_query left
    right hrel hleftSupport hrightSupport project rightState hstate input
  have hlifted : RelTriple
      (enrich <$> (sourceDirectTracedVerifierImpl input).run project)
      (id <$> (globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨
          rightResult.2.1.bad right.1.2) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2⟩
    · exact Or.inr hbad
  rw [id_map] at hlifted
  have hleft : (sourceSigningTracedVerifierImpl input).run leftState =
      enrich <$> (sourceDirectTracedVerifierImpl input).run project := by
    rfl
  rw [hleft]
  exact hlifted

theorem globalSigningMonitoredTracedStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalSigningMonitoredTracedStateRelation left right.1
      ((left.cache, []), [])
      (⟨globalFilteredCausalKeygenState right.1.1, []⟩, []) := by
  exact globalMonitoredTracedStateRelation_initial left right hrel
    hleftSupport hrightSupport

theorem evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen :
    ((fun view : ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult view.keyResult) <$>
            trajectoryProgrammedGlobalChainKeygen) =ᵈ
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
  calc
    _ =ᵈ ((fun view : ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult view.keyResult) <$>
            actualGlobalChainKeygen) :=
      evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed.symm.map _
    _ =ᵈ (Concrete.materializeCachedKeyResult <$>
          (simulateQ romImpl Concrete.keygen).run ∅) := by
      unfold actualGlobalChainKeygen
      simp [ProgrammedGlobalChainKeygenView.keyResult,
        map_eq_bind_pure_comp]
    _ =ᵈ ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) :=
      Concrete.evalDist_materialized_keygen_eq_precomputedKeygen
    _ = _ := by rfl

theorem probEvent_eq_of_evalDist_eq
    {computation₁ computation₂ : ProbComp α}
    (event : α → Prop)
    (heval : computation₁ =ᵈ computation₂) :
    Pr{let x ← computation₁}[event x] = Pr{let x ← computation₂}[event x] :=
  heval.prEvent_eq event


theorem encodingObservation?_eq_of_globalSigningCachesAgree
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialLeft initialRight finalLeft finalRight : QueryCache HashSpec)
    (hinitial : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      initialLeft initialRight)
    (hfinal : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      finalLeft finalRight)
    (output : (OracleWorld + SigningSpec).Range input) :
    encodingObservation? secretKey input (initialLeft, []) output
        (finalLeft, []) =
      encodingObservation? secretKey input (initialRight, []) output
        (finalRight, []) := by
  classical
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · rfl
    · cases hleafIndex : encodingInputLeafIndex? secretKey.parameter hashInput with
      | none => simp [encodingObservation?, hleafIndex]
      | some leafIndex =>
          obtain ⟨payload, hpayload⟩ :=
            exists_encodingInput_of_encodingInputLeafIndex?_eq_some
              secretKey.parameter hashInput leafIndex hleafIndex
          subst hashInput
          have hcache := hinitial _
            ⟨leafIndex, payload.1, payload.2, rfl⟩
          simp [encodingObservation?, hcache]
  · cases output with
    | none => rfl
    | some signature =>
        let hashInput := Concrete.CacheView.encodingInput
          secretKey.parameter request.leafIndex
          (request.message, signature.randomness)
        have hinitialCache : initialLeft hashInput = initialRight hashInput :=
          hinitial hashInput ⟨request.leafIndex, request.message,
            signature.randomness, rfl⟩
        have hfinalCache : finalLeft hashInput = finalRight hashInput :=
          hfinal hashInput ⟨request.leafIndex, request.message,
            signature.randomness, rfl⟩
        simp [encodingObservation?, hashInput, hinitialCache, hfinalCache]

theorem encodingActionTraceUpdate_eq_of_globalSigningCachesAgree
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialLeft initialRight finalLeft finalRight : QueryCache HashSpec)
    (hinitial : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      initialLeft initialRight)
    (hfinal : HashCachesAgreeOn
      (GlobalSigningComparableHashInput secretKey.parameter)
      finalLeft finalRight)
    (output : (OracleWorld + SigningSpec).Range input)
    (trace : EncodingActionTrace) :
    encodingActionTraceUpdate secretKey input (initialLeft, []) output
        (finalLeft, []) trace =
      encodingActionTraceUpdate secretKey input (initialRight, []) output
        (finalRight, []) trace := by
  unfold encodingActionTraceUpdate
  rw [encodingObservation?_eq_of_globalSigningCachesAgree secretKey input
    initialLeft initialRight finalLeft finalRight hinitial hfinal output]

abbrev SourceExactTracedState :=
  (((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) ×
    AttackerActionTrace)

def sourceExactSigningProjection
    (state : SourceExactTracedState) : SourceSigningTracedState :=
  ((state.1.1.1, state.1.1.2), state.2)

noncomputable def sourceExactQueryResult
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      SourceSigningTracedState) :
    (OracleWorld + SigningSpec).Range input × SourceExactTracedState :=
  (result.1,
    (((result.2.1,
      encodingActionTraceUpdate secretKey input
        (initialState.1.1.1, []) result.1 (result.2.1.1, [])
          initialState.1.2)), result.2.2))

theorem cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceExactTracedState) :
    (cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState =
      sourceExactQueryResult secretKey input initialState <$>
        (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
          (sourceExactSigningProjection initialState) := by
  unfold cappedBothTracedMappedAdversaryImpl
    QueryImpl.extendState appendAttackerActionTrace
    sourceSigningTracedMappedAdversaryImpl actionTracedStateImpl
    sourceExactQueryResult sourceExactSigningProjection
    cappedEncodingTracedMappedAdversaryImpl QueryImpl.extendState
  simp only [StateT.run_mk, map_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro result
  rfl

theorem encodingActionTraceUpdate_eq_of_parameter_eq
    (leftSecret rightSecret : SecretKey)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache finalCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (trace : EncodingActionTrace) :
    encodingActionTraceUpdate leftSecret input (initialCache, []) output
        (finalCache, []) trace =
      encodingActionTraceUpdate rightSecret input (initialCache, []) output
        (finalCache, []) trace := by
  unfold encodingActionTraceUpdate encodingObservation?
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · rfl
    · rw [hparameter]
  · cases output with
    | none => rfl
    | some signature => rw [hparameter]

theorem relTriple_programmed_globalHighMonitored_sourceExact_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftState) rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) rightResult.2 ∧
          leftResult.2.1.2 =
            encodingActionTraceUpdate right.1.1.secretKey input
              (rightState.1.causal.cache, []) rightResult.1
              (rightResult.2.1.causal.cache, []) leftState.1.2) ∨
        rightResult.2.1.bad right.1.2) := by
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hbase := relTriple_programmed_globalHighMonitored_signingAction left
    right hrel hleftSupport hrightSupport
    (sourceExactSigningProjection leftState) rightState hstate input
  have hlifted : RelTriple
      (sourceExactQueryResult leftSecret input leftState <$>
        (sourceSigningTracedMappedAdversaryImpl left.publicKey leftSecret
          input).run (sourceExactSigningProjection leftState))
      (id <$> (globalHighMonitoredMappedAdversaryImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) rightResult.2 ∧
          leftResult.2.1.2 =
            encodingActionTraceUpdate right.1.1.secretKey input
              (rightState.1.causal.cache, []) rightResult.1
              (rightResult.2.1.causal.cache, []) leftState.1.2) ∨
        rightResult.2.1.bad right.1.2) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · apply Or.inl
      refine ⟨hgood.1, hgood.2, ?_⟩
      obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
        _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ := hstate.1
      obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
        _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ := hgood.2.1
      have hcacheUpdate :=
        encodingActionTraceUpdate_eq_of_globalSigningCachesAgree
          leftSecret input leftState.1.1.1 rightState.1.causal.cache
          leftResult.2.1.1 rightResult.2.1.causal.cache
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hinitialCausal.1)
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hfinalCausal.1)
          leftResult.1 leftState.1.2
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      have hsecretUpdate := encodingActionTraceUpdate_eq_of_parameter_eq
        leftSecret right.1.1.secretKey
        (by simpa [leftSecret, Concrete.materializePrecomputation,
          Concrete.precomputedSecretKey] using hparameter.symm)
        input rightState.1.causal.cache rightResult.2.1.causal.cache
        leftResult.1 leftState.1.2
      simpa [sourceExactQueryResult, hgood.1] using
        hcacheUpdate.trans hsecretUpdate
    · exact Or.inr hbad
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap]
  simpa using hlifted


theorem appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
    (leftSecret rightSecret : SecretKey)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (forgery : Forgery)
    (initialLeft initialRight finalLeft finalRight : QueryCache HashSpec)
    (hinitial : HashCachesAgreeOn
      (GlobalSigningComparableHashInput leftSecret.parameter)
      initialLeft initialRight)
    (hfinal : HashCachesAgreeOn
      (GlobalSigningComparableHashInput leftSecret.parameter)
      finalLeft finalRight)
    (trace : EncodingActionTrace) :
    appendVerificationEncodingObservation leftSecret forgery
        initialLeft finalLeft trace =
      appendVerificationEncodingObservation rightSecret forgery
        initialRight finalRight trace := by
  let input := Concrete.CacheView.encodingInput leftSecret.parameter
    forgery.leafIndex (forgery.message, forgery.signature.randomness)
  let rightInput := Concrete.CacheView.encodingInput rightSecret.parameter
    forgery.leafIndex (forgery.message, forgery.signature.randomness)
  have hinput : input = rightInput := by simp [input, rightInput, hparameter]
  have hinitialCache : initialLeft input = initialRight input :=
    hinitial input ⟨forgery.leafIndex, forgery.message,
      forgery.signature.randomness, rfl⟩
  have hfinalCache : finalLeft input = finalRight input :=
    hfinal input ⟨forgery.leafIndex, forgery.message,
      forgery.signature.randomness, rfl⟩
  unfold appendVerificationEncodingObservation
  change (if initialLeft input = none then
      match finalLeft input with
      | none => trace
      | some output => trace ++ [.query forgery.leafIndex output]
    else trace) =
    (if initialRight rightInput = none then
      match finalRight rightInput with
      | none => trace
      | some output => trace ++ [.query forgery.leafIndex output]
    else trace)
  rw [← hinput, hinitialCache, hfinalCache]

noncomputable def sourceGlobalExactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceExactTracedState) := do
  let handled ← (simulateQ
    (cappedBothTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run ((((keyView.cache, []), []), []))
  let verified ← (simulateQ sourceSigningTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.leafIndex
      handled.1.message handled.1.signature)).run
        (sourceExactSigningProjection handled.2)
  let finalEncodingTrace := appendVerificationEncodingObservation
    (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
    handled.1 handled.2.1.1.1 verified.2.1.1 handled.2.1.2
  pure ((handled.1, verified.1),
    ((verified.2.1, finalEncodingTrace), verified.2.2))

def sourceGlobalExactErasedExecution
    (result : (Forgery × Bool) × SourceExactTracedState) :
    (Forgery × Bool) × SourceTracedState :=
  (result.1, (result.2.1.1.1, result.2.2))

abbrev SourceGlobalExactTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceExactTracedState)

noncomputable def sourceGlobalExactTracedProgram
    (adversary : Adversary) :
    ProbComp SourceGlobalExactTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalExactTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceGlobalExactErasedResult
    (result : SourceGlobalExactTracedProgramResult) :
    SourceGlobalTracedProgramResult :=
  (result.1, sourceGlobalExactErasedExecution result.2)

theorem sourceGlobalExactTracedDetailedExecution_projection
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    sourceGlobalExactErasedExecution <$>
        sourceGlobalExactTracedDetailedExecution adversary keyView =
      sourceGlobalTracedDetailedExecution adversary keyView := by
  unfold sourceGlobalExactTracedDetailedExecution
    sourceGlobalTracedDetailedExecution
  let secretKey :=
    Concrete.materializePrecomputation keyView.cache keyView.secretKey
  let finish : Forgery × SourceTracedState →
      ProbComp ((Forgery × Bool) × SourceTracedState) := fun handled => do
    let verified ← (simulateQ sourceDirectTracedVerifierImpl
      (Concrete.scheme.verify keyView.publicKey handled.1.leafIndex
        handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1), verified.2)
  have hprojection := cappedBothTracedMappedAdversaryImpl_actionProjection
    keyView.publicKey secretKey (adversary.main keyView.publicKey)
      (((keyView.cache, []), [])) []
  have hbound := congrArg (fun computation => computation >>= finish)
    hprojection
  simpa [secretKey, finish, sourceGlobalExactErasedExecution, map_bind,
    bind_map_left, bind_assoc, sourceSigningTracedVerifierImpl_run_eq,
    sourceDirectTracedVerifierImpl_run_eq, sourceExactSigningProjection,
    Prod.map]
    using hbound

theorem sourceGlobalExactTracedProgram_projection
    (adversary : Adversary) :
    sourceGlobalExactErasedResult <$>
        sourceGlobalExactTracedProgram adversary =
      sourceGlobalTracedProgram adversary := by
  unfold sourceGlobalExactTracedProgram sourceGlobalTracedProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalExactTracedDetailedExecution_projection]
  simp [sourceGlobalExactErasedResult, map_eq_bind_pure_comp]

theorem sourceGlobalExactErasedResult_mem_support
    (adversary : Adversary)
    {left : SourceGlobalExactTracedProgramResult}
    (hleft : left ∈ support (sourceGlobalExactTracedProgram adversary)) :
    sourceGlobalExactErasedResult left ∈
      support (sourceGlobalTracedProgram adversary) := by
  rw [← sourceGlobalExactTracedProgram_projection, support_map]
  exact ⟨left, hleft, rfl⟩

def sourceGlobalExactExecutionResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (execution : (Forgery × Bool) × SourceExactTracedState) :
    CappedBothTraceExecution :=
  (⟨keyView.publicKey,
    Concrete.materializePrecomputation keyView.cache keyView.secretKey,
    execution.1.1, execution.2.1.1.2.toSigningLog, execution.1.2⟩,
    execution.2)

def sourceGlobalExactProgramResult
    (result : SourceGlobalExactTracedProgramResult) :
    CappedBothTraceGameResult :=
  (Concrete.materializeCachedKeyResult result.1.keyResult,
    sourceGlobalExactExecutionResult result.1 result.2)

theorem sourceGlobalExactTracedDetailedExecution_eq_bothTraces
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    sourceGlobalExactExecutionResult keyView <$>
        sourceGlobalExactTracedDetailedExecution adversary keyView =
      cappedDetailedGameAfterKeygenWithBothTraces adversary keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        keyView.cache := by
  unfold sourceGlobalExactTracedDetailedExecution
    cappedDetailedGameAfterKeygenWithBothTraces
  simp only [map_bind, map_pure]
  apply bind_congr
  intro handled
  rw [sourceSigningTracedVerifierImpl_run_eq]
  simp [sourceGlobalExactExecutionResult, sourceExactSigningProjection,
    map_eq_bind_pure_comp]

theorem sourceGlobalExactTracedProgram_eq_trajectoryBothTraces
    (adversary : Adversary) :
    sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary = (do
      let keyView ← trajectoryProgrammedGlobalChainKeygen
      let execution ← cappedDetailedGameAfterKeygenWithBothTraces adversary
        keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        keyView.cache
      pure (Concrete.materializeCachedKeyResult keyView.keyResult,
        execution)) := by
  unfold sourceGlobalExactTracedProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalExactTracedDetailedExecution_eq_bothTraces]
  simp [sourceGlobalExactProgramResult, map_eq_bind_pure_comp]

theorem evalDist_sourceGlobalExact_eq_cappedBothTraces
    (adversary : Adversary) :
    (sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary) =ᵈ
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary) := by
  rw [sourceGlobalExactTracedProgram_eq_trajectoryBothTraces]
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces
  let project := fun view : ProgrammedGlobalChainKeygenView =>
    Concrete.materializeCachedKeyResult view.keyResult
  calc
    _ =ᵈ ((project <$> trajectoryProgrammedGlobalChainKeygen) >>=
        fun keyResult =>
          (fun execution => (keyResult, execution)) <$>
            cappedDetailedGameAfterKeygenWithBothTraces adversary
              keyResult.1.1 keyResult.1.2 keyResult.2) := by
      refine .of_eq ?_
      simp [project, ProgrammedGlobalChainKeygenView.keyResult,
        Concrete.materializeCachedKeyResult, map_eq_bind_pure_comp]
    _ =ᵈ (((simulateQ romImpl Concrete.scheme.keygen).run ∅) >>=
        fun keyResult =>
          (fun execution => (keyResult, execution)) <$>
            cappedDetailedGameAfterKeygenWithBothTraces adversary
              keyResult.1.1 keyResult.1.2 keyResult.2) :=
      evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen.bind_left _
    _ = _ := by
      simp only [bind_pure_comp]

def SourceWinningExactFirstLaneEvent
    (result : SourceGlobalExactTracedProgramResult) : Prop :=
  WinningExactFirstLaneBadEventOccurs
    (cappedBothEncodingProjection (sourceGlobalExactProgramResult result))

theorem cappedExactFirstLane_probability_eq_sourceGlobalExact
    (adversary : Adversary) :
    Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningExactFirstLaneBadEventOccurs x] =
      Pr{let x ← sourceGlobalExactTracedProgram adversary}[SourceWinningExactFirstLaneEvent x] := by
  calc
    _ = Pr{let x ← cappedDetailedGameWithKeygenCacheAndBothTraces adversary}[(WinningExactFirstLaneBadEventOccurs ∘ cappedBothEncodingProjection) x] := by
      rw [← cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq adversary,
        prEvent_map]
      rfl


    _ = Pr{let x ← (sourceGlobalExactProgramResult <$>
          sourceGlobalExactTracedProgram adversary)}[(WinningExactFirstLaneBadEventOccurs ∘ cappedBothEncodingProjection) x] :=
      probEvent_eq_of_evalDist_eq _
        (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary).symm
    _ = _ := by
      rw [prEvent_map]
      rfl

theorem cappedExactEncodingBranch_implies_monitorHit
    (adversary : Adversary)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hbranch : WinningOutcomeBadEventOccurs execution.2.1.1 execution.1
        .encoding ∧ ¬WinningCachedSelectionOccurs execution) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      execution.2.2 = true := by
  have hsigningMem : (execution.1, execution.2.1) ∈
      support (cappedDetailedGameWithSigningTrace adversary) := by
    rw [← cappedDetailedGameWithEncodingTrace_projection, support_map]
    exact ⟨execution, hmem, rfl⟩
  obtain ⟨entry, hentry, hprehit | hsigning | hpostSigning⟩ :=
    cappedWinning_encoding_event_trace_postSigning_decomposition adversary
      (execution.1, execution.2.1) hsigningMem hbranch.1
  · exact (hbranch.2 ⟨hbranch.1, entry, hentry, hprehit⟩).elim
  · exact cappedDetailedGameWithEncodingTrace_freshSigningCollision_monitorHit
      adversary execution hmem hbranch.1 ⟨entry, hentry, hsigning⟩
  · obtain ⟨encoding, hdecode⟩ := hbranch.1.forgery_decode
    exact
      cappedDetailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
        adversary execution hmem hbranch.1 encoding hdecode
          ⟨entry, hentry, hpostSigning⟩

theorem cappedBothTraceGameResult_keyResult_mem_support
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.1 ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, _hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyResult

theorem cappedBothTraceGameResult_cacheExecution_mem_support
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    (result.2.1, result.2.2.1.1.1) ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary result.1.1.1
          result.1.1.2)).run result.1.2) := by
  have hboth :=
    cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
      adversary result hresult
  have hencoding : (result.2.1, result.2.2.1) ∈ support
      (cappedDetailedGameAfterKeygenWithEncodingTrace adversary
        result.1.1.1 result.1.1.2 result.1.2) := by
    rw [← cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection,
      support_map]
    exact ⟨result.2, hboth, rfl⟩
  have hsigning : (result.2.1, result.2.2.1.1) ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary
        result.1.1.1 result.1.1.2 result.1.2) := by
    rw [← cappedDetailedGameAfterKeygenWithEncodingTrace_projection,
      support_map]
    exact ⟨(result.2.1, result.2.2.1), hencoding, rfl⟩
  rw [← cappedDetailedGameAfterKeygenWithSigningTrace_cache_projection,
    support_map]
  exact ⟨(result.2.1, result.2.2.1.1), hsigning, rfl⟩

end XmssSecurity.CappedChain
