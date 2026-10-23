import XmssSecurity.Proof.CappedGlobalChainHighCoverage
import XmssSecurity.Proof.StateLens

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

noncomputable def globalHighDirectUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalUniformImpl

noncomputable abbrev globalHighDirectHashFromHighImpl
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalAttackerHashQueryFromHigh high secretKey

noncomputable abbrev globalHighDirectHashImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectHashFromHighImpl
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey

noncomputable def globalHighDirectOracleExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (OracleWorld.Range input × GlobalCausalHashState) :=
  match input with
  | .inl n => (globalHighDirectUniformImpl n).run state
  | .inr hashInput =>
      (globalCausalAttackerHashQueryFromHigh
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
          hashInput).run state

noncomputable def globalHighDirectOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input state => globalHighDirectOracleExecution keyView edgeHigh input state

noncomputable def globalHighDirectSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl SigningSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun request state => globalFilteredCausalSigningQuery keyView request state

noncomputable def globalHighDirectBaseMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectOracleImpl keyView edgeHigh +
    globalHighDirectSigningImpl keyView

noncomputable def globalHighDirectVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectOracleImpl keyView edgeHigh

abbrev GlobalHighDirectKeyResult :=
  ProgrammedGlobalChainKeygenView × (GlobalChainEdgeIndex → Digest)

noncomputable def globalHighDirectKeygenAfterMaterial
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    ProbComp GlobalHighDirectKeyResult := do
  let topBase ← Concrete.sampleTopBase
  let run ← (simulateQ randomOracle (Concrete.honestKeygenFrom parameter material.1 topBase)).run
    material.2.2
  let view : ProgrammedGlobalChainKeygenView :=
    (({
      start := material.1
      table := globalChainTrajectoryMaterialTable material
      run := run
    } : CoupledGlobalChainKeygenView).toProgrammedView parameter)
  pure (view, edgeHigh)

noncomputable def globalHighDirectKeygenAfterParameter
    (parameter : PublicParameter) : ProbComp GlobalHighDirectKeyResult := do
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  let edgeHigh ← independentGlobalChainHigh
  globalHighDirectKeygenAfterMaterial parameter material edgeHigh

noncomputable def globalHighDirectKeygen :
    ProbComp GlobalHighDirectKeyResult := do
  let parameter ← Concrete.samplePublicParameter
  globalHighDirectKeygenAfterParameter parameter

abbrev GlobalHighDirectResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalCausalHashState)

attribute [local irreducible]
  programmedGlobalChainTrajectoryMaterial
  independentGlobalChainHigh
  globalChainTrajectoryMaterialTable
  CoupledGlobalChainKeygenView.toProgrammedView

theorem coupledGlobalChainKeygenWithBaseHighFull_eq_direct :
    coupledGlobalChainKeygenWithBaseHighFull = (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      pure ((keyResult.1, base), keyResult.2)) := by
  unfold coupledGlobalChainKeygenWithBaseHighFull
    coupledGlobalChainKeygenWithBaseHigh
    programmedGlobalChainTrajectoryMaterialWithBaseHigh
    programmedGlobalChainTrajectoryMaterialWithBase
    globalHighDirectKeygenAfterParameter globalHighDirectKeygenAfterMaterial
    independentGlobalChainValueTable
  simp only [bind_assoc, pure_bind]

theorem map_monitorGlobalCausalTrace_projection
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (fun result : α × GlobalMonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (monitorGlobalCausalTrace computation).run state =
      (fun result : (α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex =>
        (result.1, state.trace ++ result.2)) <$>
          computation state.causal := by
  rw [monitorGlobalCausalTrace_run, Functor.map_map]
  apply map_congr
  intro result
  simp [globalMonitoredCausalResult]

theorem map_simulate_globalMonitoredTraced_projection_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain) (state : GlobalMonitoredCausalState)
      (attackerTrace : AttackerActionTrace),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (left input).run (state, attackerTrace) =
        (fun result : ((spec.Range input × GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run state.causal)).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ left computation).run (state, attackerTrace) =
      (fun result : ((α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run state.causal)).run := by
  induction computation using OracleComp.inductionOn generalizing state
      attackerTrace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)
      let tail := fun head : ((spec.Range input × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (fun result => (result.1, head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ right (next head.1.1)).run head.1.2)).run
      change (do
        let head ← (left input).run (state, attackerTrace)
        tail (project head)) = _
      rw [← bind_map_left project]
      have hhead := hquery input state attackerTrace
      change project <$> (left input).run (state, attackerTrace) = _ at hhead
      rw [hhead, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem map_actionTracedStateImpl_globalMonitor_erased_step
    {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT GlobalMonitoredCausalState ProbComp))
    (fragment : (input : spec.Domain) → spec.Range input →
      AttackerActionTrace)
    (input : spec.Domain) (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : spec.Range input × GlobalMonitoredTracedState =>
      (result.1, result.2.1)) <$>
        (actionTracedStateImpl impl fragment input).run
          (state, attackerTrace) =
      (impl input).run state := by
  unfold actionTracedStateImpl
  simp [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc]

theorem map_globalHighMonitored_uniform_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (n : Nat)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inl n))).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalCausalUniformImpl n).run state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inl n))).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh)) attackerActionFragment
        (.inl (.inl n)) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
                GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection _ state

theorem map_globalHighMonitored_hash_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inr input))).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input
              ).run state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inr input))).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh)) attackerActionFragment
        (.inl (.inr input)) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range
                (.inl (.inr input)) × GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection _ state

theorem map_globalHighMonitored_sign_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inr request)).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inr request) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          (globalFilteredCausalSigningQuery keyView request state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inr request)).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh)) attackerActionFragment
        (.inr request) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
                GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection _ state

theorem map_simulate_globalHighMonitored_verifier_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
            computation).run state.causal)).run := by
  apply map_simulate_globalMonitoredTraced_projection_of_query
  intro input current trace
  unfold globalHighMonitoredVerifierImpl globalHighDirectVerifierImpl
  simp only [StateT.run_mk, Functor.map_map]
  unfold globalHighMonitoredBaseMappedAdversaryImpl
    globalHighDirectOracleImpl globalHighDirectOracleExecution
  rcases input with n | hashInput
  · exact map_monitorGlobalCausalTrace_projection _ current
  · exact map_monitorGlobalCausalTrace_projection _ current

def globalHighMonitoredDirectProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, result.2.2.1.causal)), result.2.2.1.trace))


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def globalHighDirectErasedResult
    (result : GlobalHighDirectResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  let keyView := result.1.1
  let execution := result.2
  ((((keyView.publicKey, keyView.secretKey), keyView.cache),
    (actionTraceOutcome keyView.publicKey keyView.secretKey
      (execution.1, []), execution.2.cache)), [])

noncomputable def globalHighDirectForgeryPrimaryProbeTrace
    (result : GlobalHighDirectResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalForgeryPrimaryProbeTrace (globalHighDirectErasedResult result)

theorem observedProbeCount_globalForgeryPrimaryProbeTrace
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    RevealProbeOracleSimulation.observedProbeCount
      (globalForgeryPrimaryProbeTrace result) = forgeryProbeCount := by
  have hcount : ∀ trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex,
      (∀ action ∈ trace, ∃ index target, action = .probe index target) →
      RevealProbeOracleSimulation.observedProbeCount trace = trace.length := by
    intro trace hprobes
    induction trace with
    | nil => rfl
    | cons action rest ih =>
        obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
        simp only [RevealProbeOracleSimulation.observedProbeCount,
          List.length_cons, Nat.succ.injEq]
        apply ih
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
  rw [hcount _ (globalForgeryPrimaryProbeTrace_all_probes result),
    globalForgeryPrimaryProbeTrace_length]

theorem observedProbeCount_globalHighDirectForgeryPrimaryProbeTrace
    (result : GlobalHighDirectResult) :
    RevealProbeOracleSimulation.observedProbeCount
        (globalHighDirectForgeryPrimaryProbeTrace result) = forgeryProbeCount := by
  unfold globalHighDirectForgeryPrimaryProbeTrace
  exact observedProbeCount_globalForgeryPrimaryProbeTrace _

theorem traceAgrees_of_all_probes
    (table : Index → Digest)
    (trace : RevealProbeOracleSimulation.ActionTrace Index)
    (hprobes : ∀ action ∈ trace, ∃ index target,
      action = .probe index target) :
    RevealProbeOracleSimulation.TraceAgrees table trace := by
  induction trace with
  | nil => trivial
  | cons action rest ih =>
      obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
      simp only [RevealProbeOracleSimulation.TraceAgrees]
      apply ih
      intro candidate hcandidate
      exact hprobes candidate (by simp [hcandidate])

theorem globalHighDirectForgeryPrimaryProbeTrace_all_probes
    (result : GlobalHighDirectResult) (action :
      RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex)
    (haction : action ∈ globalHighDirectForgeryPrimaryProbeTrace result) :
    ∃ index target, action = .probe index target := by
  exact globalForgeryPrimaryProbeTrace_all_probes _ action haction

theorem globalHighDirectForgeryPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalHighDirectResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (globalHighDirectForgeryPrimaryProbeTrace result) := by
  apply traceAgrees_of_all_probes
  intro action haction
  exact globalHighDirectForgeryPrimaryProbeTrace_all_probes result action
    haction

noncomputable def appendGlobalHighDirectPublicTrace
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      (Unit × RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) :=
  (result.1, ((), result.2.2 ++
    globalHighDirectForgeryPrimaryProbeTrace result.2.1))

theorem globalForgeryPrimaryProbeTrace_eq_of_public_fields
    (left right : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hsecret : left.1.1.1.2 = right.1.1.1.2)
    (hforgery : left.1.2.1.forgery = right.1.2.1.forgery)
    (hcache : left.1.2.2 = right.1.2.2) :
    globalForgeryPrimaryProbeTrace left =
      globalForgeryPrimaryProbeTrace right := by
  unfold globalForgeryPrimaryProbeTrace actionTracedForgeryEncoding
  rw [hsecret, hforgery, hcache]

theorem globalHighMonitored_forgeryProbeTrace_eq_direct
    (result : GlobalHighMonitoredProgramResult) :
    globalForgeryPrimaryProbeTrace (globalHighMonitoredErasedResult result) =
      globalHighDirectForgeryPrimaryProbeTrace
        (globalHighMonitoredDirectProjection result).2.1 := by
  unfold globalHighDirectForgeryPrimaryProbeTrace
  apply globalForgeryPrimaryProbeTrace_eq_of_public_fields <;> rfl

theorem globalHighMonitoredPublicProjection_eq_append_direct
    (result : GlobalHighMonitoredProgramResult) :
    globalHighMonitoredPublicProjection result =
      appendGlobalHighDirectPublicTrace
        (globalHighMonitoredDirectProjection result) := by
  unfold globalHighMonitoredPublicProjection appendGlobalHighDirectPublicTrace
    globalHighMonitoredDirectProjection
  rw [globalHighMonitored_forgeryProbeTrace_eq_direct result]
  rfl

theorem evalDist_map_congr_of_evalDist_eq
    (project : α → β) (left right : ProbComp α)
    (hdist : left =ᵈ right) :
    (project <$> left) =ᵈ (project <$> right) :=
  hdist.map project



abbrev GlobalHighDirectTracedState :=
  GlobalCausalHashState × AttackerActionTrace

noncomputable def globalHighDirectTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state => do
    let result ←
      (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run state.1
    pure (result.1,
      (result.2, state.2 ++ attackerActionFragment input result.1))

noncomputable def globalHighDirectTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (globalHighDirectVerifierImpl keyView edgeHigh input).run state.1

theorem globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

theorem map_globalHighMonitored_adversary_full_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range input ×
        GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input
            ).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      (((OracleWorld + SigningSpec).Range input × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1,
      (result.1.2, attackerTrace ++ attackerActionFragment input result.1.1)),
      result.2)
  have herased :
      (fun result : (OracleWorld + SigningSpec).Range input ×
          GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (globalHighMonitoredMappedAdversaryImpl
            ((keyView, base), edgeHigh) input).run (state, attackerTrace) =
        (fun result : (((OracleWorld + SigningSpec).Range input ×
            GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
            ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input
              ).run state.causal)).run := by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash with n | hashInput
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
          globalHighDirectUniformImpl
        exact map_globalHighMonitored_uniform_erased_projection keyView base
          edgeHigh n state attackerTrace
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
        exact map_globalHighMonitored_hash_erased_projection keyView base
          edgeHigh hashInput state attackerTrace
    · unfold globalHighDirectBaseMappedAdversaryImpl
        globalHighDirectSigningImpl
      exact map_globalHighMonitored_sign_erased_projection keyView base
        edgeHigh request state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  simpa [addAttackerTrace, globalHighMonitoredMappedAdversaryImpl,
    actionTracedStateImpl, globalHighDirectTracedMappedAdversaryImpl,
    StateT.run_mk, Functor.map_map, Function.comp_def, simulateQ_bind,
    bind_map_left, List.append_assoc] using hlifted

theorem globalHighDirectTracedVerifierImpl_run_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalHighDirectTracedState) :
    (simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, (result.2, initialState.2))) <$>
        (simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
          computation).run initialState.1 := by
  apply (StateLens.fst : StateLens GlobalHighDirectTracedState
    GlobalCausalHashState).simulateQ_run_eq
  intro input state
  rfl

noncomputable def globalHighMonitoredVerifierBaseImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld (StateT GlobalMonitoredCausalState ProbComp) :=
  fun input => globalHighMonitoredBaseMappedAdversaryImpl right (.inl input)

theorem globalHighMonitoredVerifierImpl_run_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalMonitoredTracedState) :
    (simulateQ (globalHighMonitoredVerifierImpl right)
        computation).run initialState =
      (fun result => (result.1, (result.2, initialState.2))) <$>
        (simulateQ (globalHighMonitoredVerifierBaseImpl right)
          computation).run initialState.1 := by
  apply (StateLens.fst : StateLens GlobalMonitoredTracedState
    GlobalMonitoredCausalState).simulateQ_run_eq
  intro input state
  rfl

theorem map_simulate_globalHighMonitored_verifier_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedVerifierImpl keyView edgeHigh)
            computation).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, (result.1.2, attackerTrace)), result.2)
  have herased := map_simulate_globalHighMonitored_verifier_erased_projection
    keyView base edgeHigh computation state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  rw [globalHighMonitoredVerifierImpl_run_eq] at hlifted
  rw [globalHighMonitoredVerifierImpl_run_eq]
  rw [globalHighDirectTracedVerifierImpl_run_eq]
  simpa [addAttackerTrace, Functor.map_map, Function.comp_def,
    simulateQ_map, bind_map_left] using hlifted

end XmssSecurity.CappedChain
