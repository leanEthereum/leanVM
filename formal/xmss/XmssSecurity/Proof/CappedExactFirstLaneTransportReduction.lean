import XmssSecurity.Proof.CappedExactFirstLaneSourceCoupling
import XmssSecurity.Proof.CappedGlobalFirstLaneExperiment
import XmssSecurity.Proof.CappedGlobalChainHighReduction
import XmssSecurity.Proof.CappedChain.DirectQueryAccounting
import XmssSecurity.Proof.StateLens
import XmssSecurity.Proof.EagerTraceInvariant

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

namespace GlobalHighDirectTracedState

abbrev mk (causalState : GlobalCausalHashState)
    (attackerTrace : AttackerActionTrace) : GlobalHighDirectTracedState :=
  (causalState, attackerTrace)

abbrev causalState (state : GlobalHighDirectTracedState) :
    GlobalCausalHashState := state.1

abbrev attackerTrace (state : GlobalHighDirectTracedState) :
    AttackerActionTrace := state.2

@[simp] theorem causalState_mk
    (causal : GlobalCausalHashState) (trace : AttackerActionTrace) :
    causalState (mk causal trace) = causal := rfl

@[simp] theorem attackerTrace_mk
    (causal : GlobalCausalHashState) (trace : AttackerActionTrace) :
    attackerTrace (mk causal trace) = trace := rfl

end GlobalHighDirectTracedState

@[simp] def GlobalHighDirectTracedState.initial (causalState : GlobalCausalHashState) :
    GlobalHighDirectTracedState :=
  ⟨causalState, []⟩

@[simp] def GlobalHighDirectTracedState.withCausalState (state : GlobalHighDirectTracedState)
    (causalState : GlobalCausalHashState) : GlobalHighDirectTracedState :=
  (causalState, state.2)

def globalExactTracedCausalLens :
    StateLens GlobalHighDirectTracedState GlobalCausalHashState where
  get := GlobalHighDirectTracedState.causalState
  set := GlobalHighDirectTracedState.withCausalState
  set_get state := by cases state; rfl
  get_set state nextCausal := by cases state; rfl
  set_set state left right := by cases state; rfl

@[irreducible]
noncomputable def globalExactTracedNextState
    (_keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState)
    (output : (OracleWorld + SigningSpec).Range input)
    (causalState : GlobalCausalHashState) : GlobalHighDirectTracedState :=
  GlobalHighDirectTracedState.mk causalState
    (state.attackerTrace ++ attackerActionFragment input output)

noncomputable def globalExactTracedLift {ι : Type} {world : OracleSpec ι}
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp world)
      ((OracleWorld + SigningSpec).Range input)) :
    StateT GlobalHighDirectTracedState
      (OracleComp world)
      ((OracleWorld + SigningSpec).Range input) :=
  StateT.mk fun state =>
    (fun result => (result.1,
      globalExactTracedNextState keyView input state result.1 result.2)) <$>
      base.run state.causalState

noncomputable def globalFirstLaneExactTracedSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) : QueryImpl SigningSpec
      (StateT GlobalHighDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun request => globalExactTracedLift keyView (.inr request)
    (globalFirstLaneSigningImpl keyView request)

noncomputable def globalFirstLaneExactTracedOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : QueryImpl OracleWorld
      (StateT GlobalHighDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => globalExactTracedLift keyView (.inl input)
    (StateT.mk fun state =>
      globalFirstLaneOracleExecution keyView edgeHigh input state)

noncomputable def globalFirstLaneExactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneExactTracedOracleImpl keyView edgeHigh +
    globalFirstLaneExactTracedSigningImpl keyView

noncomputable def globalFirstLaneExactTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalHighDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, state.withCausalState result.2)) <$>
      (globalFirstLaneVerifierImpl keyView edgeHigh input).run
        state.causalState

noncomputable def globalHighDirectTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalHighDirectTracedState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      (Forgery × Bool) := StateT.mk fun initial => do
  let handled ← (simulateQ
    (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)).run initial
  let verified ← (simulateQ
    (globalHighDirectTracedVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

noncomputable def globalFirstLaneExactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalHighDirectTracedState
      (OracleComp GlobalFirstLaneWorld) (Forgery × Bool) :=
  StateT.mk fun initial => do
    let handled ← (simulateQ
      (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
        (adversary.main keyView.publicKey)).run initial
    let verified ← (simulateQ
      (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1), verified.2)

abbrev GlobalExactTracedResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalHighDirectTracedState)

noncomputable def globalFirstLaneExactTracedProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld GlobalExactTracedResult := do
  let keyResult ← FirstLaneOracleSimulation.liftProbComp
    globalHighDirectKeygen
  let execution ← (globalFirstLaneExactTracedDetailedExecution adversary
    keyResult.1 keyResult.2).run
      (GlobalHighDirectTracedState.initial
        (globalFilteredCausalKeygenState keyResult.1))
  pure (keyResult, execution)

theorem globalFirstLaneErase_exactTracedLift
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (sourceBase : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (targetBase : StateT GlobalCausalHashState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalHighDirectTracedState)
    (hbase : GlobalFirstLaneErases
      (sourceBase.run state.causalState)
      (targetBase.run state.causalState)) :
    GlobalFirstLaneErases
      ((globalExactTracedLift keyView input sourceBase).run state)
      ((globalExactTracedLift keyView input targetBase).run state) := by
  unfold globalExactTracedLift
  simp only [StateT.run_mk]
  apply hbase.bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalExactTracedLift_highDirectMapped_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) :
    (globalExactTracedLift keyView input
      (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input)).run
        state =
      (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input).run
        state := by
  simp [globalHighDirectTracedMappedAdversaryImpl,
    globalExactTracedLift, globalExactTracedNextState,
    map_eq_bind_pure_comp]

theorem globalFirstLaneErase_exactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
        ).run state)
      ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input
        ).run state) := by
  rcases input with worldInput | request
  · have hbase : GlobalFirstLaneErases
        ((StateT.mk fun causalState =>
          globalFirstLaneOracleExecution keyView edgeHigh worldInput
            causalState).run state.causalState)
        ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh
          (.inl worldInput)).run state.causalState) := by
      change GlobalFirstLaneErases
        (globalFirstLaneOracleExecution keyView edgeHigh worldInput
          state.causalState)
        (globalHighDirectOracleExecution keyView edgeHigh worldInput
          state.causalState)
      exact globalFirstLaneOracleErasure keyView edgeHigh worldInput
        state.causalState
    have herasure := globalFirstLaneErase_exactTracedLift keyView
      (.inl worldInput)
      (StateT.mk fun causalState =>
        globalFirstLaneOracleExecution keyView edgeHigh worldInput causalState)
      (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh
        (.inl worldInput)) state hbase
    rw [globalExactTracedLift_highDirectMapped_eq] at herasure
    exact herasure
  · have hbase : GlobalFirstLaneErases
        ((globalFirstLaneSigningImpl keyView request).run state.causalState)
        ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh
          (.inr request)).run state.causalState) := by
      simpa [globalHighDirectBaseMappedAdversaryImpl] using
        globalFirstLaneErase_directSigningImpl keyView request
          state.causalState
    have herasure := globalFirstLaneErase_exactTracedLift keyView
      (.inr request) (globalFirstLaneSigningImpl keyView request)
      (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh
        (.inr request)) state hbase
    rw [globalExactTracedLift_highDirectMapped_eq] at herasure
    exact herasure

theorem globalFirstLaneErase_exactTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalHighDirectTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
        state)
      ((globalHighDirectTracedVerifierImpl keyView edgeHigh input).run
        state) := by
  unfold globalFirstLaneExactTracedVerifierImpl
    globalHighDirectTracedVerifierImpl
  simp only [StateT.run_mk]
  apply (globalFirstLaneOracleErasure keyView edgeHigh input
    state.causalState).bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_exactTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalHighDirectTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedDetailedExecution adversary keyView edgeHigh
        ).run state)
      ((globalHighDirectTracedDetailedExecution adversary keyView
        edgeHigh).run state) := by
  unfold globalFirstLaneExactTracedDetailedExecution
    globalHighDirectTracedDetailedExecution
  simp only [StateT.run_mk]
  apply (globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView edgeHigh)
    (adversary.main keyView.publicKey) state).bind
  intro handled
  apply (globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_exactTracedVerifierImpl keyView edgeHigh)
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature) handled.2).bind
  intro verified
  exact GlobalFirstLaneErases.pure _

noncomputable def firstLaneValidEncodingActions
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    EncodingActionTrace :=
  CappedEncodingMonitor.validActions trace.encodingActions

theorem globalFirstLaneEncodingHashQuery_validTrace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey epoch message randomness
          state)).run)) :
    firstLaneValidEncodingActions result.2 =
      CappedEncodingMonitor.validActions
        (if state.cache (Concrete.CacheView.encodingInput secretKey.parameter
            epoch (message, randomness)) = none then
          [.sign epoch result.1.1]
        else []) := by
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) with
  | some output =>
      simp [hcache, firstLaneValidEncodingActions] at hresult ⊢
      exact hresult ▸ rfl
  | none =>
      simp only [if_pos]
      dsimp only at hresult
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell,
        firstLaneValidEncodingActions] at hresult ⊢
      obtain ⟨output, _houtput, rfl⟩ := hresult
      rfl

theorem globalFirstLaneEncodingHashQuery_cacheGrowth
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey epoch message randomness
          state)).run)) :
    CacheGrowthRepresented
      (fun payload => Concrete.CacheView.encodingInput secretKey.parameter
        epoch payload)
      (fun _ output => EncodingMonitor.ObservedAction.sign epoch output)
      state.cache result.1.2.cache result.2.encodingActions ∧
    result.1.2.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) = some result.1.1 := by
  let sampledInput := Concrete.CacheView.encodingInput secretKey.parameter
    epoch (message, randomness)
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache sampledInput with
  | some output =>
      simp [sampledInput, hcache] at hresult
      subst result
      exact ⟨CacheGrowthRepresented.refl _ _ _, hcache⟩
  | none =>
      dsimp only at hresult
      simp only [sampledInput] at hcache
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact ⟨CacheGrowthRepresented.cacheQuery state.cache
        (message, randomness) output hcache (by simp),
        QueryCache.cacheQuery_self _ _ _⟩

theorem globalFirstLaneLiftRevealProbe_encodingProjection
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    Prod.map id FirstLaneOracleSimulation.ActionTrace.encodingActions <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneLiftRevealProbe computation)).run =
      (fun result => (result, ([] : EncodingActionTrace))) <$>
        simulateQ (RevealProbeOracleSimulation.eagerImpl table) computation := by
  rw [globalFirstLaneLiftRevealProbe, ← QueryImpl.simulateQ_compose]
  have htarget :
      (simulateQ ((RevealProbeOracleSimulation.eagerImpl table).withTraceAppend
        (fun _ _ => ([] : EncodingActionTrace))) computation).run =
        (fun result => (result, ([] : EncodingActionTrace))) <$>
          simulateQ (RevealProbeOracleSimulation.eagerImpl table) computation :=
    QueryImpl.run_simulateQ_withTraceAppend_const_empty
      (RevealProbeOracleSimulation.eagerImpl table) computation
  rw [← htarget]
  apply QueryImpl.mapLog_run_simulateQ_of_query
  · rfl
  · exact FirstLaneOracleSimulation.ActionTrace.encodingActions_append
  · intro input
    cases input <;>
      simp [globalFirstLaneRevealProbeImpl,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        FirstLaneOracleSimulation.uniformQuery,
        FirstLaneOracleSimulation.probeQuery,
        FirstLaneOracleSimulation.revealQuery,
        RevealProbeOracleSimulation.eagerImpl,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell]

theorem globalFirstLaneLiftRevealProbe_encodingActions_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe computation)).run)) :
    result.2.encodingActions = [] := by
  have hmapped : (result.1, result.2.encodingActions) ∈ support
      (Prod.map id FirstLaneOracleSimulation.ActionTrace.encodingActions <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneLiftRevealProbe computation)).run) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [globalFirstLaneLiftRevealProbe_encodingProjection] at hmapped
  rw [support_map] at hmapped
  obtain ⟨value, _hvalue, heq⟩ := hmapped
  exact congrArg Prod.snd heq.symm

theorem globalFirstLaneSignatureReveal_result_eq
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : Encoding)
    (signature : Signature) (state : GlobalCausalHashState)
    (result : (Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe
          ((revealGlobalSignatureChains request encoding allChains signature).run
            state))).run)) :
    result.1 = globalSignatureRevealResult table request encoding allChains
      signature state := by
  have hprojected : (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneErase
          (globalFirstLaneLiftRevealProbe
            ((revealGlobalSignatureChains request encoding allChains
              signature).run state)))).run) := by
    rw [← simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [globalFirstLaneErase_liftRevealProbe,
    simulate_eagerTrace_revealGlobalSignatureChains] at hprojected
  simp only [support_pure, Set.mem_singleton_iff] at hprojected
  exact congrArg Prod.fst hprojected

theorem globalFirstLaneSigningAttempt_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    ∃ randomness encodedHead,
      encodedHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneEncodingHashQuery keyView.secretKey request.epoch
            request.message randomness state)).run) ∧
      ((TargetSum.decodeDigest (truncateHash encodedHead.1.1) = none ∧
          result = ((none, encodedHead.1.2), encodedHead.2)) ∨
        ∃ encoding revealedHead,
          TargetSum.decodeDigest (truncateHash encodedHead.1.1) =
              some encoding ∧
            revealedHead ∈ support
              ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  ((revealGlobalSignatureChains request encoding allChains
                    (Concrete.CacheReplay.signWithEncoding keyView.cache
                      keyView.secretKey request.epoch randomness encoding)).run
                        encodedHead.1.2))).run) ∧
            revealedHead.1 =
              globalSignatureRevealResult table request encoding allChains
                (Concrete.CacheReplay.signWithEncoding keyView.cache
                  keyView.secretKey request.epoch randomness encoding)
                encodedHead.1.2 ∧
            result = ((some revealedHead.1.1, revealedHead.1.2),
              encodedHead.2 ++ revealedHead.2)) := by
  unfold globalFirstLaneSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨randomHead, hrandom, hrest⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp,
    support_map] at hrandom
  obtain ⟨randomness, _hrandomness, rfl⟩ := hrandom
  simp only [List.nil_append] at hrest
  rw [show Prod.map id (fun x => x) =
    (id : ((Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) → _)
    from Prod.map_id, id_map, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hrest
  obtain ⟨encodedHead, hencoded, htail⟩ := hrest
  rw [support_map] at htail
  obtain ⟨tailResult, htail, rfl⟩ := htail
  refine ⟨randomness, encodedHead, hencoded, ?_⟩
  cases hdecode : TargetSum.decodeDigest (truncateHash encodedHead.1.1) with
  | none =>
      simp [hdecode] at htail
      subst tailResult
      refine Or.inl ⟨rfl, ?_⟩
      simp [Prod.map]
  | some encoding =>
      simp only [hdecode] at htail
      rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at htail
      obtain ⟨revealedHead, hrevealed, hpure⟩ := htail
      simp only at hpure
      subst tailResult
      have hrevealedResult := globalFirstLaneSignatureReveal_result_eq table
        request encoding
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.epoch randomness encoding)
          encodedHead.1.2 revealedHead hrevealed
      refine Or.inr
        ⟨encoding, revealedHead, rfl, hrevealed, hrevealedResult, ?_⟩
      simp [Prod.map]

theorem globalFirstLaneAttackerHashQueryAtEpoch_trace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch)
        ).run)) :
    result.2.encodingActions =
      if state.cache input = none then [.query epoch result.1.1] else [] := by
  cases hcache : state.cache input with
  | some output =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_cached _ _ _ _ _ hcache]
        at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
  | none =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh _ _ _ _ hcache]
        at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]

theorem globalFirstLaneAttackerHashQueryAtEpoch_cacheGrowth
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtEpoch secretKey input state epoch)
        ).run)) :
    CacheGrowthRepresented
      (fun _ : Unit => input)
      (fun _ output => EncodingMonitor.ObservedAction.query epoch output)
      state.cache result.1.2.cache result.2.encodingActions ∧
    result.1.2.cache input = some result.1.1 := by
  cases hcache : state.cache input with
  | some output =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_cached _ _ _ _ _ hcache]
        at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      constructor
      · simpa [globalCausalRecordedState_cache,
          FirstLaneOracleSimulation.ActionTrace.encodingActions] using
          (CacheGrowthRepresented.refl
            (fun _ : Unit => input)
            (fun _ output => EncodingMonitor.ObservedAction.query epoch output)
            state.cache)
      · simpa only [globalCausalRecordedState_cache] using hcache
  | none =>
      rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh _ _ _ _ hcache]
        at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      constructor
      · constructor
        · simpa [GlobalCausalHashState.setCache,
            globalCausalRecordedState_cache] using
            QueryCache.le_cacheQuery state.cache hcache
        · intro _ targetOutput _hfresh hfinal
          change (state.cache.cacheQuery input output) input =
            some targetOutput at hfinal
          rw [QueryCache.cacheQuery_self] at hfinal
          have : output = targetOutput := Option.some.inj hfinal
          subst targetOutput
          simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
      · exact QueryCache.cacheQuery_self _ _ _

def GlobalFirstLaneSigningSummary
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  CacheGrowthRepresented
      (fun payload => Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch payload)
      (fun _ output => EncodingMonitor.ObservedAction.sign
        request.epoch output)
      state.cache result.1.2.cache result.2.encodingActions ∧
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions) [request.epoch] ∧
    (result.1.1 = none →
      CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions = [])

theorem globalFirstLaneSigningAttempt_summary
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    GlobalFirstLaneSigningSummary keyView request state result := by
  obtain ⟨randomness, encodedHead, hencoded, hcases⟩ :=
    globalFirstLaneSigningAttempt_support_decompose table keyView request state
      result hresult
  have hgrowth := globalFirstLaneEncodingHashQuery_cacheGrowth table
    keyView.secretKey request.epoch request.message randomness state
      encodedHead hencoded
  have htrace := globalFirstLaneEncodingHashQuery_validTrace table
    keyView.secretKey request.epoch request.message randomness state
      encodedHead hencoded
  have htrace' : CappedEncodingMonitor.validActions
      encodedHead.2.encodingActions =
        CappedEncodingMonitor.validActions
          (if state.cache
              (Concrete.CacheView.encodingInput keyView.secretKey.parameter
                request.epoch (request.message, randomness)) = none then
            [.sign request.epoch encodedHead.1.1]
          else []) := by
    simpa [firstLaneValidEncodingActions] using htrace
  rcases hcases with hreject | haccept
  · obtain ⟨hdecode, hresultEq⟩ := hreject
    subst result
    have hinvalidDigest :
        ¬TargetSum.ValidDigest (truncateHash encodedHead.1.1) := by
      intro ⟨encoding, hencoding⟩
      rw [hdecode] at hencoding
      contradiction
    have hepochs : CappedEncodingMonitor.validObservedSignEpochs
        encodedHead.2.encodingActions = [] := by
      unfold CappedEncodingMonitor.validObservedSignEpochs
      rw [htrace']
      by_cases hcache : state.cache
          (Concrete.CacheView.encodingInput keyView.secretKey.parameter
            request.epoch (request.message, randomness)) = none
      · simp [hcache, CappedEncodingMonitor.validActions,
          CappedEncodingMonitor.ActionValid, hinvalidDigest,
          EncodingMonitor.observedSignEpochs]
      · simp [hcache, CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignEpochs]
    refine ⟨hgrowth.1, ?_, ?_⟩
    · rw [hepochs]
      simp
    · intro _hnone
      exact hepochs
  · obtain ⟨encoding, revealedHead, _hdecode, hrevealed,
      hrevealedResult, hresultEq⟩ := haccept
    subst result
    have hrevealTrace : revealedHead.2.encodingActions = [] :=
      globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ _ hrevealed
    have hfinalCache : revealedHead.1.2.cache = encodedHead.1.2.cache := by
      rw [hrevealedResult, globalSignatureRevealResult_cache]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · rw [hfinalCache]
        exact hgrowth.1.1
      · intro payload output hfresh hfinal
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
        apply List.mem_append_left
        apply hgrowth.1.2 payload output hfresh
        rw [← hfinalCache]
        exact hfinal
    · unfold CappedEncodingMonitor.validObservedSignEpochs
      rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
        hrevealTrace, List.append_nil, htrace']
      by_cases hcache : state.cache
          (Concrete.CacheView.encodingInput keyView.secretKey.parameter
            request.epoch (request.message, randomness)) = none
      · simp only [hcache, if_pos]
        change List.Sublist
          (CappedEncodingMonitor.validObservedSignEpochs
            [.sign request.epoch encodedHead.1.1]) [request.epoch]
        rw [CappedEncodingMonitor.validObservedSignEpochs_singleton_sign]
        split <;> simp
      · simp [hcache, CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignEpochs]
    · intro hnone
      contradiction

theorem globalFirstLaneSignBoundedAttempts_summary
    (attempts : Nat)
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSignBoundedAttempts attempts keyView request state)
        ).run)) :
    GlobalFirstLaneSigningSummary keyView request state result := by
  induction attempts generalizing state result with
  | zero =>
      simp [globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      refine ⟨CacheGrowthRepresented.refl _ _ _, ?_, ?_⟩ <;>
        simp [CappedEncodingMonitor.validObservedSignEpochs,
          FirstLaneOracleSimulation.ActionTrace.encodingActions,
          CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignEpochs]
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attemptHead, hattempt, hcontinuation⟩ := hresult
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, rfl⟩ := hcontinuation
      have hhead := globalFirstLaneSigningAttempt_summary table keyView
        request state attemptHead hattempt
      cases hoption : attemptHead.1.1 with
      | some signature =>
          simp [hoption] at htail
          subst tailResult
          simpa [GlobalFirstLaneSigningSummary,
            FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
              using And.intro hhead.1 hhead.2.1
      | none =>
          simp only [hoption] at htail
          have htailSummary := ih attemptHead.1.2 tailResult htail
          refine ⟨?_, ?_, ?_⟩
          · simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
              using hhead.1.trans htailSummary.1
          · change List.Sublist
              (CappedEncodingMonitor.validObservedSignEpochs
                (attemptHead.2 ++ tailResult.2).encodingActions)
              [request.epoch]
            rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
              CappedEncodingMonitor.validObservedSignEpochs_append,
              hhead.2.2 hoption]
            simpa using htailSummary.2.1
          · intro hfinal
            have htailNone : tailResult.1.1 = none := by
              simpa using hfinal
            change CappedEncodingMonitor.validObservedSignEpochs
              (attemptHead.2 ++ tailResult.2).encodingActions = []
            rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
              CappedEncodingMonitor.validObservedSignEpochs_append,
              hhead.2.2 hoption, htailSummary.2.2 htailNone]
            rfl

theorem globalFirstLaneSigningQuery_cacheGrowth
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    CacheGrowthRepresented
      (fun payload => Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch payload)
      (fun _ output => EncodingMonitor.ObservedAction.sign
        request.epoch output)
      state.cache result.1.2.cache result.2.encodingActions :=
  (globalFirstLaneSignBoundedAttempts_summary signingAttemptLimit table
    keyView request state result hresult).1

theorem globalFirstLaneSigningQuery_validSignEpochs_sublist_singleton
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions) [request.epoch] :=
  (globalFirstLaneSignBoundedAttempts_summary signingAttemptLimit table
    keyView request state result hresult).2.1

theorem encodingActionTraceUpdate_sublist_of_observation_mem
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState finalState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (initialTrace externalTrace : EncodingActionTrace)
    (hrepresented : ∀ observation,
      encodingObservation? secretKey input initialState output finalState =
          some observation →
        observation ∈ externalTrace) :
    List.Sublist
      (encodingActionTraceUpdate secretKey input initialState output finalState
        initialTrace)
      (initialTrace ++ externalTrace) := by
  unfold encodingActionTraceUpdate
  cases hobservation : encodingObservation? secretKey input initialState output
      finalState with
  | none => exact List.sublist_append_left initialTrace externalTrace
  | some observation =>
      exact (List.Sublist.refl initialTrace).append
        (List.singleton_sublist.mpr (hrepresented observation hobservation))

theorem globalFirstLaneHashQuery_observation_mem
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state)).run))
    (observation : EncodingMonitor.ObservedAction)
    (hobservation : encodingObservation? keyView.secretKey
      (.inl (.inr hashInput) : (OracleWorld + SigningSpec).Domain)
      (state.cache, []) result.1.1 (result.1.2.cache, []) = some observation) :
    observation ∈ result.2.encodingActions := by
  cases hepoch : encodingInputEpoch? keyView.secretKey.parameter hashInput with
  | none =>
      by_cases hfresh : state.cache hashInput = none
      <;> simp [encodingObservation?, hfresh, hepoch] at hobservation
  | some epoch =>
      by_cases hfresh : state.cache hashInput = none
      · rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ epoch
          hepoch] at hresult
        have htrace := globalFirstLaneAttackerHashQueryAtEpoch_trace table
          keyView.secretKey hashInput state epoch result hresult
        have haction : EncodingMonitor.ObservedAction.query epoch result.1.1 ∈
            result.2.encodingActions := by
          simp [htrace, hfresh]
        have hobservation' : EncodingMonitor.ObservedAction.query epoch
            result.1.1 = observation := by
          exact Option.some.inj (by simpa [encodingObservation?, hfresh, hepoch]
            using hobservation)
        simpa [← hobservation'] using haction
      · simp [encodingObservation?, hfresh] at hobservation

theorem globalFirstLaneSigningQuery_observation_mem
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run))
    (observation : EncodingMonitor.ObservedAction)
    (hobservation : encodingObservation? keyView.secretKey
      (.inr request : (OracleWorld + SigningSpec).Domain) (state.cache, [])
      result.1.1 (result.1.2.cache, []) = some observation) :
    observation ∈ result.2.encodingActions := by
  cases houtput : result.1.1 with
  | none => simp [encodingObservation?, houtput] at hobservation
  | some signature =>
      let signedInput := Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch
          (request.message, signature.randomness)
      by_cases hfresh : state.cache signedInput = none
      · cases hfinal : result.1.2.cache signedInput with
        | none =>
            simp [encodingObservation?, signedInput, hfresh, hfinal, houtput]
              at hobservation
        | some hashOutput =>
            have hgrowth := globalFirstLaneSigningQuery_cacheGrowth table
              keyView request state result hresult
            have haction := hgrowth.2
              (request.message, signature.randomness) hashOutput
              (by simpa [signedInput] using hfresh)
              (by simpa [signedInput] using hfinal)
            have hobservation' : EncodingMonitor.ObservedAction.sign
                request.epoch hashOutput = observation := by
              exact Option.some.inj (by simpa [encodingObservation?, signedInput,
                hfresh, hfinal, houtput] using hobservation)
            simpa [← hobservation'] using haction
      · simp [encodingObservation?, signedInput, hfresh, houtput]
          at hobservation

theorem globalFirstLaneUniformQuery_trace_sublist
    (keyView : ProgrammedGlobalChainKeygenView) (n : Nat)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inl (.inl n) : (OracleWorld + SigningSpec).Domain) (state.cache, [])
          result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  simp [encodingActionTraceUpdate, encodingObservation?]

theorem globalFirstLaneHashQuery_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashInput : HashInput)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inl (.inr hashInput) : (OracleWorld + SigningSpec).Domain)
          (state.cache, []) result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  apply encodingActionTraceUpdate_sublist_of_observation_mem
  intro observation hobservation
  exact globalFirstLaneHashQuery_observation_mem table keyView edgeHigh
    hashInput state result hresult observation hobservation

theorem globalFirstLaneSigningQuery_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inr request : (OracleWorld + SigningSpec).Domain) (state.cache, [])
          result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  apply encodingActionTraceUpdate_sublist_of_observation_mem
  intro observation hobservation
  exact globalFirstLaneSigningQuery_observation_mem table keyView request
    state result hresult observation hobservation

theorem globalExactTracedLift_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalHighDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView input base).run state)).run))
    (hbaseSub : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      List.Sublist
        (encodingActionTraceUpdate keyView.secretKey input
          (state.causalState.cache, []) baseResult.1.1
            (baseResult.1.2.cache, []) initialTrace)
        (initialTrace ++ baseResult.2.encodingActions)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey input
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  unfold globalExactTracedLift at hresult
  rw [StateT.run_mk, simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  subst result
  unfold globalExactTracedNextState
  simpa using hbaseSub baseResult hbase

abbrev GlobalFirstLaneOracleTraceSublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop :=
  ∀ (input : OracleWorld.Domain)
    (state : GlobalCausalHashState) (encodingTrace : EncodingActionTrace)
    (result : (OracleWorld.Range input × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
    result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneOracleExecution keyView edgeHigh input state)).run) →
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inl input)
        (state.cache, []) result.1.1 (result.1.2.cache, []) encodingTrace)
      (encodingTrace ++ result.2.encodingActions)

theorem globalFirstLaneOracleTraceSublist_holds
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneOracleTraceSublist table keyView edgeHigh := by
  intro input state encodingTrace result hresult
  cases input with
  | inl n =>
      exact globalFirstLaneUniformQuery_trace_sublist keyView n state
        encodingTrace result
  | inr hashInput =>
      exact globalFirstLaneHashQuery_trace_sublist table keyView edgeHigh
        hashInput state encodingTrace result hresult

abbrev GlobalFirstLaneExactTracedOracleTraceSublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop :=
  ∀ (input : OracleWorld.Domain)
    (state : GlobalHighDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : (OracleWorld.Range input × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
    result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedOracleImpl keyView edgeHigh input).run
          state)).run) →
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inl input)
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions)

theorem globalFirstLaneExactTracedOracleTraceSublist_holds
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneExactTracedOracleTraceSublist table keyView edgeHigh := by
  intro input state initialTrace result hresult
  unfold globalFirstLaneExactTracedOracleImpl at hresult
  apply globalExactTracedLift_trace_sublist table keyView
    (.inl input)
    (StateT.mk fun causalState =>
      globalFirstLaneOracleExecution keyView edgeHigh input causalState)
    state initialTrace result hresult
  exact globalFirstLaneOracleTraceSublist_holds table keyView edgeHigh
    input state.causalState initialTrace

theorem globalFirstLaneExactTracedSigningImpl_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalHighDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : (SigningSpec.Range request × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
          ).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inr request)
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  unfold globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_trace_sublist table keyView
    (.inr request) (globalFirstLaneSigningImpl keyView request) state
      initialTrace result hresult
  intro baseResult hbase
  exact globalFirstLaneSigningQuery_trace_sublist table keyView request
    state.causalState initialTrace baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
          ).run state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey input
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  cases input with
  | inl worldInput =>
      exact globalFirstLaneExactTracedOracleTraceSublist_holds table keyView
        edgeHigh worldInput state initialTrace result hresult
  | inr request =>
      exact globalFirstLaneExactTracedSigningImpl_trace_sublist table keyView
        request state initialTrace result hresult

theorem globalFirstLaneLiftRevealProbe_mem_eagerTrace_support
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe computation)).run)) :
    (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run) := by
  rw [← globalFirstLaneErase_liftRevealProbe computation,
    ← simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
  exact ⟨result, hresult, rfl⟩

theorem globalFirstLaneHashQuery_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state)).run)) :
    state.cache ≤ result.1.2.cache := by
  cases hepoch : encodingInputEpoch? keyView.secretKey.parameter hashInput with
  | some epoch =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ epoch
        hepoch] at hresult
      exact (globalFirstLaneAttackerHashQueryAtEpoch_cacheGrowth table
        keyView.secretKey hashInput state epoch result hresult).1.1
  | none =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ _ hepoch]
        at hresult
      have hprojected := globalFirstLaneLiftRevealProbe_mem_eagerTrace_support
        table ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput).run state) result hresult
      exact
        simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_cache_le
          table (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            hashInput state (result.1, result.2.chainActions) hprojected

@[irreducible]
noncomputable def globalFirstLaneVerifierHashExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (state : GlobalCausalHashState) : OracleComp GlobalFirstLaneWorld
      (HashOutput × GlobalCausalHashState) :=
  globalFirstLaneAttackerHashQueryFromHighRun
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
      state

theorem globalFirstLaneVerifierHashExecution_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashInput : HashInput) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  unfold globalFirstLaneVerifierHashExecution at hresult
  exact globalFirstLaneHashQuery_cache_le table keyView edgeHigh hashInput state
    result hresult

theorem simulateQ_eagerTrace_state_cache_le
    {spec : OracleSpec ι} {State : Type}
    (table : GlobalChainValueIndex → Digest)
    (implRun : ∀ input : spec.Domain, State →
      OracleComp GlobalFirstLaneWorld (spec.Range input × State))
    (stateCache : State → QueryCache HashSpec)
    (hstep : ∀ (input : spec.Domain) (state : State)
      (result : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (implRun input state)).run) →
      stateCache state ≤ stateCache result.1.2)
    (computation : OracleComp spec α) (initialState : State)
    (result : (α × State) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun input => StateT.mk (implRun input)) computation).run
          initialState)).run)) :
    stateCache initialState ≤ stateCache result.1.2 := by
  apply simulateQ_eagerTrace_support_invariant table
    (fun input => StateT.mk (implRun input))
    (fun initial _trace final => stateCache initial ≤ stateCache final)
  · intro state
    exact le_rfl
  · intro initial middle final headTrace tailTrace hhead htail
    exact hhead.trans htail
  · exact hstep
  · exact hresult

theorem globalFirstLaneVerifierHashExecution_simulateQ_cache_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp HashSpec α)
    (initialState : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun hashInput => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
            computation).run initialState)).run)) :
    initialState.cache ≤ result.1.2.cache := by
  exact simulateQ_eagerTrace_state_cache_le table
    (globalFirstLaneVerifierHashExecution keyView edgeHigh)
      (fun state : GlobalCausalHashState => state.cache)
      (globalFirstLaneVerifierHashExecution_cache_le table keyView edgeHigh)
      computation initialState result hresult

@[irreducible]
noncomputable def concreteVerificationAfterDigest
    (publicKey : PublicKey) (epoch : Epoch) (signature : Signature)
    (digest : Digest) : OracleComp HashSpec Bool :=
  match TargetSum.decodeDigest digest with
  | none => pure false
  | some encoding => do
      let endpoints ← Concrete.recoverEndpoints publicKey.parameter epoch
        encoding signature
      let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
      Concrete.verifyAfterLeaf publicKey epoch signature leaf

theorem concreteVerify_eq_encodingHash_bind_afterDigest
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    (Concrete.verify publicKey epoch message signature :
        OracleComp HashSpec Bool) = (do
      let digest ← Concrete.encodingHash publicKey.parameter epoch message
        signature.randomness
      concreteVerificationAfterDigest publicKey epoch signature digest) := by
  unfold Concrete.verify concreteVerificationAfterDigest
  rfl

theorem globalFirstLaneVerifier_eq_hashExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (forgery : Forgery) :
    simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
        (Concrete.scheme.verify keyView.publicKey forgery.epoch
          forgery.message forgery.signature) =
      simulateQ (fun hashInput => StateT.mk
        (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
        (Concrete.verify keyView.publicKey forgery.epoch forgery.message
          forgery.signature : OracleComp HashSpec Bool) := by
  change simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
      (liftM (Concrete.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature : OracleComp HashSpec Bool)) = _
  rw [← OracleComp.liftComp_eq_liftM]
  trans simulateQ (globalFirstLaneHashImpl keyView edgeHigh)
    (Concrete.verify keyView.publicKey forgery.epoch forgery.message
      forgery.signature : OracleComp HashSpec Bool)
  · apply QueryImpl.simulateQ_liftComp_right_eq_of_apply
    intro hashInput
    exact globalFirstLaneVerifierImpl_hash keyView edgeHigh hashInput
  · congr 1
    funext hashInput
    unfold globalFirstLaneVerifierHashExecution
    rfl

theorem concreteEncodingHash_eq_query
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (randomness : Randomness) :
    (Concrete.encodingHash parameter epoch message randomness :
        OracleComp HashSpec Digest) = (do
      let output ← HasQuery.query (spec := HashSpec)
        (tweakableHashInput parameter (.encoding epoch)
          (Concrete.encodingPayload message randomness))
      pure (truncateHash output)) := by
  unfold Concrete.encodingHash Concrete.tweakableHash Concrete.oracleHash
  rfl

theorem simulateQ_eagerTrace_query_pure_support_decompose
    {spec : OracleSpec ι} {State β : Type}
    (table : GlobalChainValueIndex → Digest)
    (implRun : ∀ input : spec.Domain, State →
      OracleComp GlobalFirstLaneWorld (spec.Range input × State))
    (input : spec.Domain) (finish : spec.Range input → β)
    (initialState : State)
    (result : (β × State) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun queryInput => StateT.mk (implRun queryInput)) (do
          let output ← (OracleSpec.query input :
            OracleComp spec (spec.Range input))
          pure (finish output))).run initialState)).run)) :
    ∃ queryHead : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (implRun input initialState)).run) ∧
      result = ((finish queryHead.1.1, queryHead.1.2), queryHead.2) := by
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨queryHead, hquery, hrest⟩ := hresult
  rw [support_map] at hrest
  obtain ⟨tail, htail, rfl⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
    support_pure, Set.mem_singleton_iff] at htail
  subst tail
  rw [simulateQ_spec_query] at hquery
  refine ⟨queryHead, hquery, ?_⟩
  simp only [Prod.map_apply, id_eq]
  rw [show (∅ : FirstLaneOracleSimulation.ActionTrace
    GlobalChainValueIndex) = [] by rfl, List.append_nil]

theorem globalFirstLaneEncodingHash_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (initialState : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (fun hashInput => StateT.mk
          (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
            (Concrete.encodingHash keyView.publicKey.parameter epoch message
              randomness : OracleComp HashSpec Digest)).run initialState)
                ).run)) :
    ∃ queryHead : (HashOutput × GlobalCausalHashState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneVerifierHashExecution keyView edgeHigh
            (tweakableHashInput keyView.publicKey.parameter (.encoding epoch)
              (Concrete.encodingPayload message randomness)) initialState)).run) ∧
      result = ((truncateHash queryHead.1.1, queryHead.1.2), queryHead.2) := by
  rw [concreteEncodingHash_eq_query] at hresult
  exact simulateQ_eagerTrace_query_pure_support_decompose table
    (globalFirstLaneVerifierHashExecution keyView edgeHigh)
      (tweakableHashInput keyView.publicKey.parameter (.encoding epoch)
        (Concrete.encodingPayload message randomness)) truncateHash
      initialState result hresult

theorem globalFirstLaneVerifier_support_decompose_raw
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (initialState : GlobalCausalHashState)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run initialState)).run)) :
    ∃ (queryHead : (HashOutput × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
      (tail : (Bool × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneVerifierHashExecution keyView edgeHigh
            (tweakableHashInput keyView.publicKey.parameter
              (.encoding forgery.epoch)
              (Concrete.encodingPayload forgery.message
                forgery.signature.randomness)) initialState)).run) ∧
      tail ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (fun hashInput => StateT.mk
            (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
              (concreteVerificationAfterDigest keyView.publicKey forgery.epoch
                forgery.signature (truncateHash queryHead.1.1))).run
                  queryHead.1.2)).run) ∧
      result = (tail.1, queryHead.2 ++ tail.2) := by
  rw [globalFirstLaneVerifier_eq_hashExecution keyView edgeHigh forgery]
    at hresult
  rw [concreteVerify_eq_encodingHash_bind_afterDigest] at hresult
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
    WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  rw [support_map] at htail
  obtain ⟨tail, htail, rfl⟩ := htail
  obtain ⟨queryHead, hquery, rfl⟩ :=
    globalFirstLaneEncodingHash_support_decompose table keyView edgeHigh
      forgery.epoch forgery.message forgery.signature.randomness initialState
        head hhead
  refine ⟨queryHead, tail, hquery, ?_, ?_⟩
  · simpa using htail
  · cases tail
    rfl

theorem globalFirstLaneVerifier_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (initialState : GlobalCausalHashState)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run initialState)).run)) :
    ∃ (queryHead : (HashOutput × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
      (tail : (Bool × GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
      queryHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneAttackerHashQueryAtEpoch keyView.secretKey
            (Concrete.CacheView.encodingInput keyView.secretKey.parameter
              forgery.epoch
                (forgery.message, forgery.signature.randomness))
            initialState forgery.epoch)).run) ∧
      tail ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (fun hashInput => StateT.mk
            (globalFirstLaneVerifierHashExecution keyView edgeHigh hashInput))
              (concreteVerificationAfterDigest keyView.publicKey forgery.epoch
                forgery.signature (truncateHash queryHead.1.1))).run
                  queryHead.1.2)).run) ∧
      result = (tail.1, queryHead.2 ++ tail.2) := by
  obtain ⟨queryHead, tail, hquery, htail, hresultEq⟩ :=
    globalFirstLaneVerifier_support_decompose_raw table keyView edgeHigh
      forgery initialState result hresult
  let targetInput := Concrete.CacheView.encodingInput
    keyView.secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)
  have hqueryInput :
      tweakableHashInput keyView.publicKey.parameter
          (.encoding forgery.epoch)
          (Concrete.encodingPayload forgery.message
            forgery.signature.randomness) = targetInput := by
    simp [targetInput, Concrete.CacheView.encodingInput, hparameter]
  rw [hqueryInput] at hquery
  unfold globalFirstLaneVerifierHashExecution at hquery
  have hepoch : encodingInputEpoch? keyView.secretKey.parameter targetInput =
      some forgery.epoch := by
    simp [targetInput]
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _
    forgery.epoch hepoch] at hquery
  refine ⟨queryHead, tail, ?_, htail, hresultEq⟩
  · simpa [targetInput] using hquery

theorem globalFirstLaneVerifier_freshEncoding_mem_trace
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (initialState : GlobalCausalHashState)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (result : (Bool × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (targetOutput : HashOutput)
    (hfresh : initialState.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        forgery.epoch (forgery.message, forgery.signature.randomness)) = none)
    (hfinal : result.1.2.cache
      (Concrete.CacheView.encodingInput keyView.secretKey.parameter
        forgery.epoch (forgery.message, forgery.signature.randomness)) =
          some targetOutput)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run initialState)).run)) :
    .query forgery.epoch targetOutput ∈ result.2.encodingActions := by
  obtain ⟨queryHead, tail, hquery, htail, rfl⟩ :=
    globalFirstLaneVerifier_support_decompose table keyView edgeHigh forgery
      initialState hparameter result hresult
  let targetInput := Concrete.CacheView.encodingInput
    keyView.secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)
  have hhead := globalFirstLaneAttackerHashQueryAtEpoch_cacheGrowth table
    keyView.secretKey targetInput initialState forgery.epoch queryHead hquery
  have htailLe := globalFirstLaneVerifierHashExecution_simulateQ_cache_le
    table keyView edgeHigh
      (concreteVerificationAfterDigest keyView.publicKey forgery.epoch
        forgery.signature (truncateHash queryHead.1.1))
      queryHead.1.2 tail htail
  have htailGrowth : CacheGrowthRepresented
      (fun _ : Unit => targetInput)
      (fun _ output => EncodingMonitor.ObservedAction.query forgery.epoch output)
      queryHead.1.2.cache tail.1.2.cache tail.2.encodingActions := by
    constructor
    · exact htailLe
    · intro _ output hfreshMiddle _hfinal
      have hcached := (globalFirstLaneAttackerHashQueryAtEpoch_cacheGrowth
        table keyView.secretKey targetInput initialState forgery.epoch
          queryHead hquery).2
      rw [hcached] at hfreshMiddle
      contradiction
  have hgrowth := hhead.1.trans htailGrowth
  simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions_append] using
    hgrowth.2 () targetOutput
      (by simpa [targetInput] using hfresh)
      (by simpa [targetInput] using hfinal)

theorem globalFirstLaneExactTracedVerifierImpl_run_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalHighDirectTracedState) :
    (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run state =
      (fun result => (result.1, state.withCausalState result.2)) <$>
        (globalFirstLaneVerifierImpl keyView edgeHigh input).run
          state.causalState := by
  unfold globalFirstLaneExactTracedVerifierImpl
  rfl

theorem globalFirstLaneExactTracedVerifier_simulateQ_run_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalHighDirectTracedState) :
    (simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
        computation).run state =
      (fun result => (result.1, state.withCausalState result.2)) <$>
        (simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          computation).run state.causalState := by
  exact globalExactTracedCausalLens.simulateQ_run_eq
    (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
    (globalFirstLaneVerifierImpl keyView edgeHigh)
    (globalFirstLaneExactTracedVerifierImpl_run_eq_map keyView edgeHigh)
    computation state

theorem globalFirstLaneExactTracedVerifier_eager_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalHighDirectTracedState)
    (result : (α × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
            computation).run state)).run)) :
    ∃ baseResult : (α × GlobalCausalHashState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
            computation).run state.causalState)).run) ∧
      result = ((baseResult.1.1, state.withCausalState baseResult.1.2),
        baseResult.2) := by
  rw [globalFirstLaneExactTracedVerifier_simulateQ_run_eq_map] at hresult
  rw [simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  exact ⟨baseResult, hbase, heq.symm⟩

theorem globalFirstLaneExactTracedVerifier_append_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery)
    (state : GlobalHighDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (hparameter : keyView.publicKey.parameter = keyView.secretKey.parameter)
    (result : (Bool × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run state)).run)) :
    List.Sublist
      (appendVerificationEncodingObservation keyView.secretKey forgery
        state.causalState.cache result.1.2.causalState.cache
          initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  obtain ⟨baseResult, hbase, heq⟩ :=
    globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
      edgeHigh
      (Concrete.scheme.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature)
      state result hresult
  subst result
  let forgedInput := Concrete.CacheView.encodingInput
    keyView.secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)
  by_cases hfresh : state.causalState.cache forgedInput = none
  · cases houtput : baseResult.1.2.cache forgedInput with
    | none =>
        simp [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput]
    | some output =>
        have haction := globalFirstLaneVerifier_freshEncoding_mem_trace table
          keyView edgeHigh forgery state.causalState hparameter baseResult
            output (by simpa [forgedInput] using hfresh)
              (by simpa [forgedInput] using houtput) hbase
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput] using
            (List.Sublist.refl initialTrace).append
              (List.singleton_sublist.mpr haction)
  · simp [appendVerificationEncodingObservation, forgedInput, hfresh]

theorem globalFirstLaneUniformImpl_run
    (n : Nat) (state : GlobalCausalHashState) :
    (globalFirstLaneUniformImpl n).run state = (do
      let output ← FirstLaneOracleSimulation.uniformQuery n
      pure (output, state)) := by
  rfl

theorem globalFirstLaneUniformImpl_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneUniformImpl n).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  rw [globalFirstLaneUniformImpl_run] at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  simp [FirstLaneOracleSimulation.uniformQuery,
    FirstLaneOracleSimulation.eagerTraceImpl,
    FirstLaneOracleSimulation.eagerImpl,
    FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _houtput, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst result
  simp [CappedEncodingMonitor.validObservedSignEpochs,
    FirstLaneOracleSimulation.ActionTrace.encodingActions,
    CappedEncodingMonitor.validActions,
    EncodingMonitor.observedSignEpochs]

theorem globalFirstLaneHashRun_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (high : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (input : HashInput) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
        ).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  cases hepoch : encodingInputEpoch? secretKey.parameter input with
  | none =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey
        input state hepoch] at hresult
      have htrace := globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)
          result hresult
      rw [htrace]
      simp [CappedEncodingMonitor.validObservedSignEpochs,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  | some epoch =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
        input state epoch hepoch] at hresult
      have htrace := globalFirstLaneAttackerHashQueryAtEpoch_trace table
        secretKey input state epoch result hresult
      rw [htrace]
      split
      · exact CappedEncodingMonitor.validObservedSignEpochs_singleton_query
          epoch result.1.1
      · rfl

theorem globalExactTracedLift_eager_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView input base).run state)).run)) :
    ∃ baseResult : ((OracleWorld + SigningSpec).Range input ×
        GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) ∧
      result = ((baseResult.1.1,
        globalExactTracedNextState keyView input state baseResult.1.1
          baseResult.1.2), baseResult.2) := by
  unfold globalExactTracedLift at hresult
  rw [StateT.run_mk, simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  exact ⟨baseResult, hbase, heq.symm⟩

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput) :
    globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
        (.inl (.inr input)) =
      globalExactTracedLift keyView (.inl (.inr input))
        (StateT.mk (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
            input)) := by
  rfl

theorem globalExactTracedHash_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      HashOutput)
    (state : GlobalHighDirectTracedState)
    (result : (HashOutput × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl (.inr input)) base).run
          state)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions = []) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl (.inr input)) base state result hresult
  have htraceEq := congrArg (fun candidate =>
    CappedEncodingMonitor.validObservedSignEpochs
      candidate.2.encodingActions) hresultEq
  exact htraceEq.trans (hnil baseResult hbase)

theorem globalExactTracedHash_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      HashOutput)
    (state : GlobalHighDirectTracedState)
    (result : (HashOutput × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl (.inr input)) base).run
          state)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions = []) :
    List.Sublist
      ((state.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  have htrace :=
    globalExactTracedHash_validSignEpochs_eq_nil table keyView
      input base state result hresult hnil
  obtain ⟨_baseResult, _hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl (.inr input)) base state result hresult
  have hstateEq : result.1.2.attackerTrace =
      state.attackerTrace ++ [AttackerAction.hash input] := by
    have hstateEq' := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, attackerActionFragment] using hstateEq'
  have hstate : result.1.2.attackerTrace.toSigningLog.map
      (fun entry => entry.1.epoch) =
      state.attackerTrace.toSigningLog.map (fun entry => entry.1.epoch) := by
    rw [hstateEq, AttackerActionTrace.toSigningLog_append, List.map_append]
    simp [AttackerActionTrace.toSigningLog, AttackerAction.signingEntry?]
  rw [htrace, List.append_nil, hstate]

theorem globalExactTracedLift_oracle_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (worldInput : OracleWorld.Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (OracleWorld.Range worldInput))
    (initialState : GlobalHighDirectTracedState)
    (result : (OracleWorld.Range worldInput ×
      GlobalHighDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl worldInput) base).run
          initialState)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run initialState.causalState)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions = []) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl worldInput) base initialState result hresult
  have houtputEq : result.1.1 = baseResult.1.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hresultEq
  have hstate : result.1.2.attackerTrace =
      initialState.attackerTrace ++
        attackerActionFragment (.inl worldInput) result.1.1 := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, houtputEq] using hstateEq
  have htrace : CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
    have htraceEq := congrArg (fun candidate =>
      CappedEncodingMonitor.validObservedSignEpochs
        candidate.2.encodingActions) hresultEq
    rw [htraceEq]
    exact hnil baseResult hbase
  rw [htrace, List.append_nil, hstate,
    AttackerActionTrace.toSigningLog_append, List.map_append]
  simp [attackerActionFragment, AttackerActionTrace.toSigningLog,
    AttackerAction.signingEntry?]

theorem globalExactTracedLift_signing_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (SigningSpec.Range request))
    (initialState : GlobalHighDirectTracedState)
    (result : (SigningSpec.Range request × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inr request) base).run
          initialState)).run))
    (hsub : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run initialState.causalState)).run) →
      List.Sublist (CappedEncodingMonitor.validObservedSignEpochs
        baseResult.2.encodingActions) [request.epoch]) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inr request) base initialState result hresult
  have houtputEq : result.1.1 = baseResult.1.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hresultEq
  have hstate : result.1.2.attackerTrace =
      initialState.attackerTrace ++
        attackerActionFragment (.inr request) result.1.1 := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, houtputEq] using hstateEq
  have htraceSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions) [request.epoch] := by
    have htraceEq := congrArg (fun candidate =>
      CappedEncodingMonitor.validObservedSignEpochs
        candidate.2.encodingActions) hresultEq
    rw [htraceEq]
    exact hsub baseResult hbase
  have happended := (List.Sublist.refl
    (initialState.attackerTrace.toSigningLog.map
      fun entry => entry.1.epoch)).append htraceSub
  rw [hstate]
  simpa [AttackerActionTrace.toSigningLog_append,
    attackerActionFragment, AttackerActionTrace.toSigningLog,
    AttackerAction.signingEntry?] using happended

theorem globalFirstLaneExactTracedMappedAdversaryImpl_uniform_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat)
    (initialState : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
      GlobalHighDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inl n))).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedOracleImpl at hresult
  apply globalExactTracedLift_oracle_validSignEpochs_step table
    keyView (.inl n)
    (StateT.mk fun causalState =>
      globalFirstLaneOracleExecution keyView edgeHigh (.inl n) causalState)
    initialState result hresult
  intro baseResult hbase
  exact globalFirstLaneUniformImpl_validSignEpochs_eq_nil table n
    initialState.causalState baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversaryImpl_signing_validSignEpochs_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (request : SignRequest)
    (initialState : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range (.inr request) ×
      GlobalHighDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inr request)).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_signing_validSignEpochs_step table
    keyView request (globalFirstLaneSigningImpl keyView request)
      initialState result hresult
  intro baseResult hbase
  exact globalFirstLaneSigningQuery_validSignEpochs_sublist_singleton table
    keyView request initialState.causalState baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist_of_hashRun
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashRun : HashInput → GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState))
    (hhashEq : ∀ input,
      globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inr input)) =
        globalExactTracedLift keyView (.inl (.inr input))
          (StateT.mk (hashRun input)))
    (hhashNil : ∀ input state result,
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (hashRun input state)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions = [])
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalHighDirectTracedState)
    (result : (α × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  apply simulateQ_eagerTrace_support_invariant table
    (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
    (fun initial trace final => List.Sublist
      ((initial.attackerTrace.toSigningLog.map fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs trace.encodingActions)
      (final.attackerTrace.toSigningLog.map fun entry => entry.1.epoch))
  · intro state
    simp [CappedEncodingMonitor.validObservedSignEpochs,
      FirstLaneOracleSimulation.ActionTrace.encodingActions,
      CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]
  · intro initial middle final headTrace tailTrace hhead htail
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append]
    simpa [List.append_assoc] using
      (hhead.append (List.Sublist.refl
        (CappedEncodingMonitor.validObservedSignEpochs
          tailTrace.encodingActions))).trans htail
  · intro input state stepResult hstep
    cases input with
    | inl worldInput =>
        cases worldInput with
        | inl n =>
            exact
              globalFirstLaneExactTracedMappedAdversaryImpl_uniform_validSignEpochs_step
                table keyView edgeHigh n state stepResult hstep
        | inr hashInput =>
            rw [hhashEq] at hstep
            apply globalExactTracedHash_validSignEpochs_step table keyView
              hashInput (StateT.mk (hashRun hashInput)) state stepResult hstep
            intro baseResult hbase
            exact hhashNil hashInput state.causalState baseResult hbase
    | inr request =>
        exact
          globalFirstLaneExactTracedMappedAdversaryImpl_signing_validSignEpochs_step
            table keyView edgeHigh request state stepResult hstep
  · exact hresult

theorem globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalHighDirectTracedState)
    (result : (α × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignEpochs
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  exact
    globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist_of_hashRun
      table keyView edgeHigh
        (globalFirstLaneAttackerHashQueryFromHighRun
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
        (globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run keyView
          edgeHigh)
        (globalFirstLaneHashRun_validSignEpochs_eq_nil table
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
        computation initialState result hresult

theorem globalFirstLaneVerifierImpl_hash_eq_run
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput) :
    globalFirstLaneVerifierImpl keyView edgeHigh (.inr input) =
      StateT.mk (globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input) := by
  rfl

theorem globalFirstLaneVerifier_validSignEpochs_eq_nil_of_hashRun
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashRun : HashInput → GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState))
    (hhashEq : ∀ input,
      globalFirstLaneVerifierImpl keyView edgeHigh (.inr input) =
        StateT.mk (hashRun input))
    (hhashNil : ∀ input state result,
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (hashRun input state)).run) →
      CappedEncodingMonitor.validObservedSignEpochs
        result.2.encodingActions = [])
    (computation : OracleComp OracleWorld α)
    (state : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          computation).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  apply simulateQ_eagerTrace_support_invariant table
    (globalFirstLaneVerifierImpl keyView edgeHigh)
    (fun _initial trace _final =>
      CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions = [])
  · intro state
    simp [CappedEncodingMonitor.validObservedSignEpochs,
      FirstLaneOracleSimulation.ActionTrace.encodingActions,
      CappedEncodingMonitor.validActions, EncodingMonitor.observedSignEpochs]
  · intro initial middle final headTrace tailTrace hhead htail
    simp [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append, hhead, htail]
  · intro input state stepResult hstep
    cases input with
    | inl n =>
        unfold globalFirstLaneVerifierImpl globalFirstLaneOracleImpl
          globalFirstLaneOracleExecution at hstep
        exact globalFirstLaneUniformImpl_validSignEpochs_eq_nil table n state
          stepResult hstep
    | inr input =>
        rw [hhashEq] at hstep
        exact hhashNil input state stepResult hstep
  · exact hresult

theorem globalFirstLaneVerifier_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalCausalHashState)
    (result : (α × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
          computation).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  exact globalFirstLaneVerifier_validSignEpochs_eq_nil_of_hashRun table
    keyView edgeHigh
      (globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
      (globalFirstLaneVerifierImpl_hash_eq_run keyView edgeHigh)
      (globalFirstLaneHashRun_validSignEpochs_eq_nil table
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey)
      computation state result hresult

theorem globalFirstLaneExactTracedVerifier_validSignEpochs_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalHighDirectTracedState)
    (result : (α × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
            computation).run state)).run)) :
    CappedEncodingMonitor.validObservedSignEpochs
      result.2.encodingActions = [] := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalFirstLaneExactTracedVerifier_eager_support_decompose table keyView
      edgeHigh computation state result hresult
  have htraceEq := congrArg (fun candidate =>
    CappedEncodingMonitor.validObservedSignEpochs
      candidate.2.encodingActions) hresultEq
  exact htraceEq.trans
    (globalFirstLaneVerifier_validSignEpochs_eq_nil table keyView edgeHigh
      computation state.causalState baseResult hbase)


set_option maxRecDepth 1000000

theorem globalExactTracedLift_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalHighDirectTracedState)
    (fuel : Nat)
    (hbase : (base.run state.causalState).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery fuel) :
    ((globalExactTracedLift keyView input base).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery fuel := by
  unfold globalExactTracedLift
  simp only [StateT.run_mk]
  rw [map_eq_bind_pure_comp]
  apply OracleComp.isQueryBoundP_bind (n := fuel) (m := 0) hbase
  intro result _hresult
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneExactTracedOracleImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedOracleImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  unfold globalFirstLaneExactTracedOracleImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneOracleExecution_hazardBound keyView edgeHigh input
    state.causalState

theorem globalFirstLaneExactTracedSigningImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneExactTracedSigningImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneSigningImpl_hazardBound keyView request
    state.causalState

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input).run
      state).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (directHashActionCost input) := by
  rcases input with (worldInput | request)
  · rcases worldInput with uniformInput | hashInput
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
      simpa [directHashActionCost] using
        globalFirstLaneExactTracedOracleImpl_hazardBound keyView edgeHigh
          (.inl uniformInput) state
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
      simpa [directHashActionCost] using
        globalFirstLaneExactTracedOracleImpl_hazardBound keyView edgeHigh
          (.inr hashInput) state
  · unfold globalFirstLaneExactTracedMappedAdversaryImpl
    simpa [directHashActionCost] using
      globalFirstLaneExactTracedSigningImpl_hazardBound keyView request state

theorem globalFirstLaneExactTracedVerifierImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  rw [globalFirstLaneExactTracedVerifierImpl_run_eq_map]
  rw [map_eq_bind_pure_comp]
  apply OracleComp.isQueryBoundP_bind
    (n := if input matches .inr _ then 1 else 0) (m := 0)
    (globalFirstLaneOracleImpl_hazardBound keyView edgeHigh input
      state.causalState)
  intro result _hresult
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0


set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem map_globalHighMonitored_adversary_exact_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalHighDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run state =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
            input).run (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  exact map_globalHighMonitored_adversary_full_query keyView base edgeHigh
    input state.1 state.2

theorem map_simulate_globalHighMonitored_exact_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec
      (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain)
      (state : GlobalMonitoredTracedState),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)) <$>
          (left input).run state =
        (fun result : ((spec.Range input ×
            GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.1.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run
              (GlobalHighDirectTracedState.mk state.1.causal state.2))).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ left computation).run state =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run
            (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result :
          spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)
      let tail := fun head : ((spec.Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (fun result => (result.1, head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ right (next head.1.1)).run head.1.2)).run
      change (do
        let head ← (left input).run state
        tail (project head)) = _
      rw [← bind_map_left project]
      have hhead := hquery input state
      change project <$> (left input).run state = _ at hhead
      rw [hhead, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem map_simulate_globalHighMonitored_adversary_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run
              (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  apply map_simulate_globalHighMonitored_exact_of_query
  exact map_globalHighMonitored_adversary_exact_query keyView base edgeHigh

theorem map_simulate_globalHighMonitored_verifier_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedVerifierImpl keyView edgeHigh)
            computation).run
              (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  exact map_simulate_globalHighMonitored_verifier_full_projection keyView
    base edgeHigh computation state.1 state.2

set_option maxHeartbeats 3000000 in
theorem map_globalHighMonitoredDetailedExecution_full_projection
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (fun result : (Forgery × Bool) × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        globalHighMonitoredDetailedExecution adversary
          ((keyView, base), edgeHigh) =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectTracedDetailedExecution adversary keyView
          edgeHigh).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState keyView)))).run := by
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView, []⟩, [])
  let project := fun result : Forgery × GlobalMonitoredTracedState =>
    ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
      result.2.1.trace)
  let tail := fun head : ((Forgery × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    (fun result : ((Bool × GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
      (((head.1.1, result.1.1), result.1.2), head.2 ++ result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey head.1.1.epoch
            head.1.1.message head.1.1.signature)).run head.1.2)).run
  have htail (handled : Forgery × GlobalMonitoredTracedState) :
      (do
        let verified ← (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh))
          (Concrete.scheme.verify keyView.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure (((handled.1, verified.1),
          GlobalHighDirectTracedState.mk verified.2.1.causal verified.2.2),
            verified.2.1.trace)) = tail (project handled) := by
    have hvertifier :=
      map_simulate_globalHighMonitored_verifier_exact keyView
        base edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature) handled.2
    simpa [tail, project, Functor.map_map] using
      congrArg
      (fun candidate =>
        (fun result : ((Bool × GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$>
          candidate)
        hvertifier
  unfold globalHighMonitoredDetailedExecution
    globalHighDirectTracedDetailedExecution
  simp only [map_bind, StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    map_pure]
  simp_rw [htail]
  change (do
    let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial
    tail (project handled)) = _
  rw [← bind_map_left project]
  have hhead :=
    map_simulate_globalHighMonitored_adversary_exact keyView
      base edgeHigh (adversary.main keyView.publicKey) initial
  change project <$>
    (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail]

def globalHighMonitoredFullProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, GlobalHighDirectTracedState.mk result.2.2.1.causal
        result.2.2.2)), result.2.2.1.trace))


def globalHighDirectExactTracedBaseProjection
    (result : GlobalExactTracedResult) : GlobalHighDirectResult :=
  (result.1, (result.2.1, result.2.2.causalState))

noncomputable def globalHighDirectExactForgeryPrimaryProbeTrace
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalHighDirectForgeryPrimaryProbeTrace
    (globalHighDirectExactTracedBaseProjection result)

noncomputable def appendGlobalHighDirectExactPublicTrace
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1, (result.2.1, result.2.2 ++
    globalHighDirectExactForgeryPrimaryProbeTrace result.2.1))


noncomputable def globalFirstLaneExactTracedPublicProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld GlobalExactTracedResult := do
  let result ← globalFirstLaneExactTracedProgram adversary
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectExactForgeryPrimaryProbeTrace result))
  pure result


theorem globalHighDirectExactForgeryPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (globalHighDirectExactForgeryPrimaryProbeTrace result) := by
  unfold globalHighDirectExactForgeryPrimaryProbeTrace
  exact globalHighDirectForgeryPrimaryProbeTrace_agrees table _


theorem globalHighMonitored_fullProjection_public_eq
    (result : GlobalHighMonitoredProgramResult) :
    let projected := appendGlobalHighDirectExactPublicTrace
      (globalHighMonitoredFullProjection result)
    (projected.1, ((), projected.2.2)) =
      globalHighMonitoredPublicProjection result := by
  rw [globalHighMonitoredPublicProjection_eq_append_direct]
  rfl

theorem globalHighExactEncodingEvent_implies_combinedHit
    (table : GlobalChainValueIndex → Digest)
    (encodingTrace : EncodingActionTrace)
    (attackerTrace : AttackerActionTrace)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hencodingSub : List.Sublist encodingTrace trace.encodingActions)
    (hvalidSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions)
      (attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch))
    (hvalid : SigningTranscript.Valid attackerTrace.toSigningLog)
    (hhit : CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      encodingTrace = true) :
    FirstLaneOracleSimulation.CombinedHit table trace := by
  apply Or.inl
  have hnodup :
      (CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions).Nodup := by
    exact hvalidSub.nodup hvalid
  exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
    hencodingSub hnodup hhit

abbrev GlobalFirstLaneExactPublicEagerResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)


noncomputable def globalFirstLaneExactPublicEagerExperiment
    (adversary : Adversary) :
    ProbComp GlobalFirstLaneExactPublicEagerResult :=
  FirstLaneOracleSimulation.eagerExperiment
    (globalFirstLaneExactTracedPublicProgram adversary)

end XmssSecurity.CappedChain
