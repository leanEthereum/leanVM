import XmssSecurity.Proof.CappedExactFirstLaneTransportReduction
import XmssSecurity.Proof.BoundedFirstLaneCoupling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

theorem verifierHashQueryCost_eq_if (input : OracleWorld.Domain) :
    verifierHashQueryCost input =
      (if input matches .inr _ then 1 else 0) := by
  rcases input with n | hashInput <;> rfl

def globalFirstLaneExactFullProjection {α : Type}
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (result : (α × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (α × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (result.1, chainPrefix ++ result.2.chainActions)

theorem map_eagerTrace_erasure_eq {α : Type}
    (base : GlobalChainValueIndex → Digest)
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (firstLane : OracleComp GlobalFirstLaneWorld
      (α × GlobalHighDirectTracedState))
    (direct : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (α × GlobalHighDirectTracedState))
    (herase : GlobalFirstLaneErases firstLane direct) :
    (fun result => (result.1, chainPrefix ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          direct).run =
      globalFirstLaneExactFullProjection chainPrefix <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          firstLane).run := by
  have htarget :=
    simulate_globalFirstLaneEagerTrace_chainProjection base firstLane
  rw [herase] at htarget
  have htarget' := congrArg
    (fun computation =>
      (fun result => (result.1, chainPrefix ++ result.2)) <$> computation)
    htarget
  unfold globalFirstLaneExactFullProjection
  simpa [Functor.map_map, Function.comp_def] using htarget'.symm

theorem map_globalHighMonitored_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (highState : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalHighDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run highState =
      globalFirstLaneExactFullProjection highState.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
            input).run (GlobalHighDirectTracedState.mk highState.1.causal
              highState.2))).run := by
  have hhigh := map_globalHighMonitored_adversary_exact_query keyView base
    edgeHigh input highState
  have herase := globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView
    edgeHigh input
      (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
  rw [hhigh]
  exact map_eagerTrace_erasure_eq base highState.1.trace _ _ herase

theorem relTriple_globalHighMonitored_firstLane_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (highState : GlobalMonitoredTracedState) :
    RelTriple
      ((globalHighMonitoredMappedAdversaryImpl
        ((keyView, base), edgeHigh) input).run highState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          input).run (GlobalHighDirectTracedState.mk highState.1.causal
            highState.2))).run)
      (fun highResult firstLaneResult =>
        ((highResult.1, GlobalHighDirectTracedState.mk
            highResult.2.1.causal highResult.2.2),
            highResult.2.1.trace) =
          globalFirstLaneExactFullProjection highState.1.trace
            firstLaneResult ∧
        highResult ∈ support
          ((globalHighMonitoredMappedAdversaryImpl
            ((keyView, base), edgeHigh) input).run highState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
              input).run (GlobalHighDirectTracedState.mk highState.1.causal
                highState.2))).run)) := by
  classical
  letI : DecidableEq
      (((OracleWorld + SigningSpec).Range input ×
        GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalHighMonitored_action_eq_firstLane keyView base edgeHigh input
      highState)

def globalStateOfFirstLane
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex) : GlobalMonitoredTracedState :=
  (⟨firstLaneState.causalState, trace.chainActions⟩,
    firstLaneState.attackerTrace)

theorem globalStateOfFirstLane_eq
    (highState : GlobalMonitoredTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : firstLaneState = GlobalHighDirectTracedState.mk
      highState.1.causal highState.2)
    (htrace : trace.chainActions = highState.1.trace) :
    globalStateOfFirstLane firstLaneState trace = highState := by
  subst firstLaneState
  rcases highState with ⟨⟨causal, chainTrace⟩, attackerTrace⟩
  change trace.chainActions = chainTrace at htrace
  subst chainTrace
  rfl

structure GlobalFirstLaneProjectionFacts {Result : Type}
    (history : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (highResult : Result × GlobalMonitoredTracedState)
    (firstLaneResult : (Result × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop where
  output : highResult.1 = firstLaneResult.1.1
  causal : highResult.2.1.causal = firstLaneResult.1.2.causalState
  attacker : highResult.2.2 = firstLaneResult.1.2.attackerTrace
  chain : highResult.2.1.trace =
    history.chainActions ++ firstLaneResult.2.chainActions
  state : globalStateOfFirstLane firstLaneResult.1.2
    (history ++ firstLaneResult.2) = highResult.2

theorem GlobalFirstLaneProjectionFacts.of_projection {Result : Type}
    (history : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (highResult : Result × GlobalMonitoredTracedState)
    (firstLaneResult : (Result × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hprojection :
      ((highResult.1, GlobalHighDirectTracedState.mk
        highResult.2.1.causal highResult.2.2), highResult.2.1.trace) =
        globalFirstLaneExactFullProjection history.chainActions
          firstLaneResult) :
    GlobalFirstLaneProjectionFacts history highResult firstLaneResult := by
  have hchain : highResult.2.1.trace =
      history.chainActions ++ firstLaneResult.2.chainActions := by
    simpa [globalFirstLaneExactFullProjection] using
      congrArg Prod.snd hprojection
  refine ⟨congrArg (fun result => result.1.1) hprojection,
    congrArg (fun result => result.1.2.causalState) hprojection,
    congrArg (fun result => result.1.2.attackerTrace) hprojection,
    hchain, ?_⟩
  apply globalStateOfFirstLane_eq
  · exact congrArg (fun result => result.1.2) hprojection |>.symm
  · rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append]
    exact hchain.symm

theorem GlobalFirstLaneProjectionFacts.combinedHit_of_bad {Result : Type}
    {history : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex}
    {highResult : Result × GlobalMonitoredTracedState}
    {firstLaneResult : (Result × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex}
    (hfacts : GlobalFirstLaneProjectionFacts history highResult firstLaneResult)
    (base : GlobalChainValueIndex → Digest)
    (hbad : highResult.2.1.bad base) :
    FirstLaneOracleSimulation.CombinedHit base
      (history ++ firstLaneResult.2) := by
  right
  rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
    ← hfacts.chain]
  exact highResult.2.1.bad_implies_runObserved base hbad

def SourceFirstLaneExactGoodStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  GlobalSigningMonitoredTracedStateRelation left right
      (sourceExactSigningProjection leftState)
      (globalStateOfFirstLane firstLaneState trace) ∧
    List.Sublist leftState.1.2 trace.encodingActions ∧
    List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs trace.encodingActions)
      (firstLaneState.attackerTrace.toSigningLog.map fun entry => entry.1.epoch)

theorem cappedBothTracedMappedAdversaryImpl_cache_projection
    (publicKey : PublicKey) (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : SourceExactTracedState) :
    (fun result => (result.1, result.2.1.1.1)) <$>
      (cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state =
        (simulateQ romImpl (sourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run state.1.1.1 := by
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap,
    sourceSigningTracedMappedAdversaryImpl_query_eq_map]
  simp only [Functor.map_map, sourceExactQueryResult, sourceSigningTracedQueryResult,
    sourceSigningTracedStateProjection, sourceExactSigningProjection]
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
  simp only [StateT.run_mk, map_bind, map_pure]
  rw [sourceDirectMappedAdversaryImpl_eq_compose]
  simp only [QueryImpl.apply_compose, Prod.mk.eta, bind_pure]


theorem relTriple_sourceExact_firstLane_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2
          input).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input ∧
          leftResult.2.2.hashInputs.length =
            leftState.2.hashInputs.length + directHashActionCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.1.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input)) := by
  let highState := globalStateOfFirstLane firstLaneState trace
  have hsourceHigh : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftState) highState := hstate.1
  have hencodingTrace := hstate.2.1
  have hvalidEpochs := hstate.2.2
  have hsource :=
    relTriple_programmed_globalHighMonitored_sourceExact_action left right hrel
      hleftSupport hrightSupport leftState highState hsourceHigh input
  have hhigh := relTriple_globalHighMonitored_firstLane_action
    right.1.1 right.1.2 right.2 input highState
  apply relTriple_post_mono (relTriple_trans_exists hsource hhigh)
  intro leftResult firstLaneResult hglued
  obtain ⟨highResult, hsourceResult, hhighResult⟩ := hglued
  obtain ⟨hprojection, hhighSupport, hfirstLaneSupport⟩ := hhighResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ directHashActionCost input :=
    FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.1.2
      ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2
        input).run (GlobalHighDirectTracedState.mk highState.1.causal
          highState.2))
      (directHashActionCost input)
      (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1.1
        right.2 input (GlobalHighDirectTracedState.mk highState.1.causal
          highState.2))
      firstLaneResult hfirstLaneSupport
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + directHashActionCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hhighActionTrace :=
    globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq right
      input highState highResult hhighSupport
  have hfirstLaneEncodingSub :=
    globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist
      right.1.2 right.1.1 right.2 input
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
          leftState.1.2 firstLaneResult hfirstLaneSupport
  have hprojectionFacts :=
    GlobalFirstLaneProjectionFacts.of_projection trace highResult
      firstLaneResult (by
        simpa [highState, globalStateOfFirstLane] using hprojection)
  have hfragmentValid :=
    globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist
      right.1.2 right.1.1 right.2 (liftM (OracleSpec.query input))
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
          firstLaneResult
          (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
  have hnextValidEpochs : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        (trace ++ firstLaneResult.2).encodingActions)
      (highResult.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append,
      hprojectionFacts.attacker]
    exact (hvalidEpochs.append (List.Sublist.refl _)).trans hfragmentValid
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount, ?_⟩
    · exact congrArg (fun result => result.1.1) hprojection
    · have hnextEncodingTrace : List.Sublist leftResult.2.1.2
          (trace ++ firstLaneResult.2).encodingActions := by
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
        rw [hgood.2.2, hprojectionFacts.output, hprojectionFacts.causal]
        exact hfirstLaneEncodingSub.trans
          (hencodingTrace.append (List.Sublist.refl _))
      refine ⟨?_, hnextEncodingTrace, ?_⟩
      · rw [hprojectionFacts.state]
        exact hgood.2.1
      · simpa [← hprojectionFacts.attacker] using hnextValidEpochs
    · have hinitialTrace : leftState.2 = highState.2 := hsourceHigh.2
      have hfinalTrace : leftResult.2.2 = highResult.2.2 := hgood.2.1.2
      rw [hfinalTrace, hhighActionTrace, ← hinitialTrace,
        AttackerActionTrace.hashInputs_append, List.length_append,
        attackerActionFragment_hashInputs_length]
  · apply Or.inr
    exact ⟨hprojectionFacts.combinedHit_of_bad right.1.2 hbad, htotalCount⟩


def sourceExactVerifierResult
    (initialState : SourceExactTracedState)
    (result : OracleWorld.Range input × SourceSigningTracedState) :
    OracleWorld.Range input × SourceExactTracedState :=
  (result.1, ((result.2.1, initialState.1.2), result.2.2))

noncomputable def sourceExactTracedVerifierImpl : QueryImpl OracleWorld
    (StateT SourceExactTracedState ProbComp) := fun input =>
  StateT.mk fun state => sourceExactVerifierResult state <$>
    (sourceSigningTracedVerifierImpl input).run
      (sourceExactSigningProjection state)

theorem sourceExactTracedVerifierImpl_cache_projection (input : OracleWorld.Domain)
    (state : SourceExactTracedState) :
    (fun result => (result.1, result.2.1.1.1)) <$> (sourceExactTracedVerifierImpl input).run state =
      (romImpl input).run state.1.1.1 := by
  simp only [sourceExactTracedVerifierImpl, StateT.run_mk,
    sourceSigningTracedVerifierImpl_query_run_eq, Functor.map_map,
    sourceExactVerifierResult, sourceExactSigningProjection]
  exact id_map _

theorem sourceExactTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceExactTracedState) :
    (simulateQ sourceExactTracedVerifierImpl computation).run initialState =
      (fun result : α × SourceSigningTracedState =>
        (result.1, ((result.2.1, initialState.1.2), result.2.2))) <$>
        (simulateQ sourceSigningTracedVerifierImpl computation).run
          (sourceExactSigningProjection initialState) := by
  let lens : StateLens SourceExactTracedState SourceSigningTracedState :=
    ⟨sourceExactSigningProjection,
      fun state nextSigning => ((nextSigning.1, state.1.2), nextSigning.2),
      by
        intro state
        rcases state with ⟨⟨⟨cache, signingTrace⟩, encodingTrace⟩, actionTrace⟩
        rfl,
      by simp [sourceExactSigningProjection],
      by simp⟩
  apply lens.simulateQ_run_eq
  intro input state
  rfl

theorem relTriple_programmed_globalHighMonitored_sourceExact_verifier_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (highState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftState) highState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceExactTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run highState)
      (fun leftResult highResult =>
        (leftResult.1 = highResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) highResult.2 ∧
          leftResult.2.1.2 = leftState.1.2) ∨
        highResult.2.1.bad right.1.2) := by
  have hbase :=
    relTriple_programmed_globalHighMonitored_signingVerifierQuery left right
      hrel hleftSupport hrightSupport
        (sourceExactSigningProjection leftState) highState hstate input
  let enrich : OracleWorld.Range input × SourceSigningTracedState →
      OracleWorld.Range input × SourceExactTracedState :=
    sourceExactVerifierResult leftState
  have hlifted : RelTriple
      (enrich <$>
        (sourceSigningTracedVerifierImpl input).run
          (sourceExactSigningProjection leftState))
      (id <$> (globalHighMonitoredVerifierImpl right input).run highState)
      (fun leftResult highResult =>
        (leftResult.1 = highResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) highResult.2 ∧
          leftResult.2.1.2 = leftState.1.2) ∨
        highResult.2.1.bad right.1.2) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult highResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, by
        simpa [enrich, sourceExactVerifierResult,
          sourceExactSigningProjection] using hgood.2, rfl⟩
    · exact Or.inr hbad
  rw [id_map] at hlifted
  have hleft : (sourceExactTracedVerifierImpl input).run leftState =
      enrich <$>
        (sourceSigningTracedVerifierImpl input).run
          (sourceExactSigningProjection leftState) := by rfl
  rw [hleft]
  exact hlifted

theorem map_globalHighMonitored_verifier_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (highState : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalHighDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh) input).run highState =
      globalFirstLaneExactFullProjection highState.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
            (GlobalHighDirectTracedState.mk highState.1.causal
              highState.2))).run := by
  have hhigh := map_simulate_globalHighMonitored_verifier_exact keyView base
    edgeHigh (liftM (OracleWorld.query input)) highState
  simp only [simulateQ_spec_query] at hhigh
  have herase := globalFirstLaneErase_exactTracedVerifierImpl keyView edgeHigh
    input (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
  rw [hhigh]
  exact map_eagerTrace_erasure_eq base highState.1.trace _ _ herase

theorem relTriple_globalHighMonitored_firstLane_verifier_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (highState : GlobalMonitoredTracedState) :
    RelTriple
      ((globalHighMonitoredVerifierImpl
        ((keyView, base), edgeHigh) input).run highState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
          (GlobalHighDirectTracedState.mk highState.1.causal
            highState.2))).run)
      (fun highResult firstLaneResult =>
        ((highResult.1, GlobalHighDirectTracedState.mk
            highResult.2.1.causal highResult.2.2),
            highResult.2.1.trace) =
          globalFirstLaneExactFullProjection highState.1.trace
            firstLaneResult ∧
        highResult ∈ support
          ((globalHighMonitoredVerifierImpl
            ((keyView, base), edgeHigh) input).run highState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
              (GlobalHighDirectTracedState.mk highState.1.causal
                highState.2))).run)) := by
  classical
  letI : DecidableEq
      ((OracleWorld.Range input × GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalHighMonitored_verifier_action_eq_firstLane keyView base
      edgeHigh input highState)

theorem relTriple_sourceExact_firstLane_verifier_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : OracleWorld.Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used) :
    RelTriple
      ((sourceExactTracedVerifierImpl input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input).run
          firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + verifierHashQueryCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.1.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + verifierHashQueryCost input)) := by
  let highState := globalStateOfFirstLane firstLaneState trace
  have hsourceHigh : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftState) highState := hstate.1
  have hencodingTrace := hstate.2.1
  have hvalidEpochs := hstate.2.2
  have hsource :=
    relTriple_programmed_globalHighMonitored_sourceExact_verifier_action
      left right
      hrel hleftSupport hrightSupport leftState highState hsourceHigh input
  have hhigh :=
    relTriple_globalHighMonitored_firstLane_verifier_action right.1.1
      right.1.2 right.2 input highState
  apply relTriple_post_mono (relTriple_trans_exists hsource hhigh)
  intro leftResult firstLaneResult hglued
  obtain ⟨highResult, hsourceResult, hhighResult⟩ := hglued
  obtain ⟨hprojection, hhighSupport, hfirstLaneSupport⟩ := hhighResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ verifierHashQueryCost input := by
    apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.1.2
      ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input).run
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2))
      (verifierHashQueryCost input) _ firstLaneResult hfirstLaneSupport
    change ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input
      ).run (GlobalHighDirectTracedState.mk highState.1.causal
        highState.2)).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery (verifierHashQueryCost input)
    rw [verifierHashQueryCost_eq_if]
    exact globalFirstLaneExactTracedVerifierImpl_hazardBound right.1.1
      right.2 input
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + verifierHashQueryCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hfragmentValid :=
    globalFirstLaneExactTracedVerifier_validSignEpochs_eq_nil right.1.2
      right.1.1 right.2 (liftM (OracleSpec.query input))
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
          firstLaneResult
          (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
  have hprojectionFacts :=
    GlobalFirstLaneProjectionFacts.of_projection trace highResult
      firstLaneResult (by
        simpa [highState, globalStateOfFirstLane] using hprojection)
  have hfirstAttacker : firstLaneResult.1.2.attackerTrace =
      highState.2 := by
    obtain ⟨baseResult, _hbase, hresultEq⟩ :=
      globalFirstLaneExactTracedVerifier_eager_support_decompose right.1.2
        right.1.1 right.2 (liftM (OracleSpec.query input))
          (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
            firstLaneResult
            (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
    rw [hresultEq]
    rfl
  have hnextValidEpochs : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        (trace ++ firstLaneResult.2).encodingActions)
      (highResult.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append,
      hfragmentValid, List.append_nil, hprojectionFacts.attacker]
    rw [hfirstAttacker]
    exact hvalidEpochs
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount⟩
    · exact hprojectionFacts.output
    · have hnextEncodingTrace : List.Sublist leftResult.2.1.2
          (trace ++ firstLaneResult.2).encodingActions := by
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
          hgood.2.2]
        exact hencodingTrace.trans (List.sublist_append_left _ _)
      refine ⟨?_, hnextEncodingTrace, ?_⟩
      · rw [hprojectionFacts.state]
        exact hgood.2.1
      · simpa [← hprojectionFacts.attacker] using hnextValidEpochs
  · apply Or.inr
    exact ⟨hprojectionFacts.combinedHit_of_bad right.1.2 hbad, htotalCount⟩

theorem relTriple_sourceExact_firstLane_verifier_boundedHit
    (countLimit hitLimit used fuel : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp OracleWorld α)
    (leftState : SourceExactTracedState)
    (hbound : HashQueryBound computation leftState.1.1.1 fuel)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ sourceExactTracedVerifierImpl computation).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
          computation).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ firstLaneResult.2))) := by
  let leftFinish := fun (value : α) (state : SourceExactTracedState) =>
    (pure (value, state) : ProbComp (α × SourceExactTracedState))
  let rightFinish := fun (value : α) (state : GlobalHighDirectTracedState) =>
    (pure (value, state) : OracleComp GlobalFirstLaneWorld
      (α × GlobalHighDirectTracedState))
  have hgeneric := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    sourceExactTracedVerifierImpl
    (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
    leftFinish rightFinish verifierHashQueryCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun _state _spent => True)
    (fun rest remaining state => HashQueryBound rest state.1.1.1 remaining)
    (by
      intro input next remaining state result hrest hresult
      have hr : (result.1, result.2.1.1.1) ∈ support ((romImpl input).run state.1.1.1) := by
        rw [← sourceExactTracedVerifierImpl_cache_projection, support_map]
        exact ⟨result, hresult, rfl⟩
      have h := hashQueryBound_query_bind input next state.1.1.1 remaining hrest _ hr
      cases input <;> simpa [verifierHashQueryCost] using h)
    (by
      intro spent input state firstState history hstates hprefix _haccounted
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_verifier_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2, True.intro⟩
      · exact Or.inr hhit)
    countLimit hitLimit
    (by
      intro value spent remaining state firstState history _hremaining hstates
        hprefix _haccounted htotal
      simp only [leftFinish, rightFinish, simulateQ_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, by simpa using hstates, by
        simpa using hprefix.trans (by omega : spent ≤ countLimit)⟩)
    used fuel computation leftState firstLaneState hbound trace hstate hcount
      True.intro htotal hlimits
  simpa [leftFinish, rightFinish] using hgeneric

def sourceAppendVerificationState
    (secretKey : SecretKey) (forgery : Forgery)
    (initialState finalState : SourceExactTracedState) :
    SourceExactTracedState :=
  ((finalState.1.1,
    appendVerificationEncodingObservation secretKey forgery
      initialState.1.1.1 finalState.1.1.1 finalState.1.2), finalState.2)

def firstLaneAppendVerificationState
    (_secretKey : SecretKey) (_forgery : Forgery)
    (_initialState finalState : GlobalHighDirectTracedState) :
    GlobalHighDirectTracedState :=
  finalState

theorem SourceFirstLaneExactGoodStateRelation.appendVerification
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (forgery : Forgery)
    (leftInitial leftFinal : SourceExactTracedState)
    (firstLaneInitial firstLaneFinal : GlobalHighDirectTracedState)
    (initialTrace finalTrace :
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      leftInitial firstLaneInitial initialTrace)
    (hfinal : SourceFirstLaneExactGoodStateRelation left right.1
      leftFinal firstLaneFinal finalTrace)
    (happendSub : List.Sublist
      (appendVerificationEncodingObservation right.1.1.secretKey forgery
        firstLaneInitial.causalState.cache
          firstLaneFinal.causalState.cache leftFinal.1.2)
      finalTrace.encodingActions) :
    SourceFirstLaneExactGoodStateRelation left right.1
      (sourceAppendVerificationState
        (Concrete.materializePrecomputation left.cache left.secretKey)
          forgery leftInitial leftFinal)
      (firstLaneAppendVerificationState right.1.1.secretKey forgery
        firstLaneInitial firstLaneFinal) finalTrace := by
  let highInitial := globalStateOfFirstLane firstLaneInitial initialTrace
  let highFinal := globalStateOfFirstLane firstLaneFinal finalTrace
  have hsourceInitial : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftInitial) highInitial := hinitial.1
  have hsourceFinal : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftFinal) highFinal := hfinal.1
  have hvalidFinal := hfinal.2.2
  obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
    _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ :=
      hsourceInitial.1
  obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
    _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ :=
      hsourceFinal.1
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  have happend :=
    appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
      leftSecret right.1.1.secretKey
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey] using hparameter.symm)
      forgery leftInitial.1.1.1 highInitial.1.causal.cache
        leftFinal.1.1.1 highFinal.1.causal.cache
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hinitialCausal.1)
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hfinalCausal.1)
      leftFinal.1.2
  let nextEncodingTrace := appendVerificationEncodingObservation leftSecret
    forgery leftInitial.1.1.1 leftFinal.1.1.1 leftFinal.1.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [sourceAppendVerificationState, sourceExactSigningProjection,
      highFinal, globalStateOfFirstLane,
      firstLaneAppendVerificationState] using hsourceFinal
  · change List.Sublist nextEncodingTrace finalTrace.encodingActions
    unfold nextEncodingTrace
    rw [happend]
    simpa [highInitial, highFinal, globalStateOfFirstLane,
      firstLaneAppendVerificationState] using happendSub
  · simpa [firstLaneAppendVerificationState] using hvalidFinal

theorem relTriple_sourceExact_firstLane_detailedExecution_boundedHit
    (countLimit hitLimit : Nat)
    (adversary : Adversary)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hsourceBound :
      HashQueryBound (sourceUnloggedDetailedGameAfterKeygen adversary
        (Concrete.materializeCachedKeyResult left.keyResult).1.1
        (Concrete.materializeCachedKeyResult left.keyResult).1.2)
          (Concrete.materializeCachedKeyResult left.keyResult).2 countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
          right.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult firstLaneResult =>
        ((leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 firstLaneResult.2 ∧
          FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
            countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            firstLaneResult.2))) := by
  let secretKey :=
    Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let highInitial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let firstLaneInitial : GlobalHighDirectTracedState :=
    GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      sourceInitial firstLaneInitial [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, highInitial, firstLaneInitial,
        globalStateOfFirstLane, sourceExactSigningProjection,
        FirstLaneOracleSimulation.ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel
          hleftSupport hrightSupport
    · simp [sourceInitial,
        FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [CappedEncodingMonitor.validObservedSignEpochs,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.scheme.verify
      left.publicKey forgery.epoch forgery.message forgery.signature
  let Budget := fun
    (rest : OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : Nat) (state : SourceExactTracedState) =>
      HashQueryBound (simulateQ
        (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey) rest >>=
          finish) state.1.1.1 remaining
  let leftFinish := fun (forgery : Forgery)
    (initial : SourceExactTracedState) => do
      let verified ← (simulateQ sourceSigningTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
          forgery.signature)).run (sourceExactSigningProjection initial)
      pure ((forgery, verified.1),
        ((verified.2.1,
          appendVerificationEncodingObservation secretKey forgery
            initial.1.1.1 verified.2.1.1 initial.1.2), verified.2.2))
  let rightFinish := fun (forgery : Forgery)
    (initial : GlobalHighDirectTracedState) => do
      let verified ← (simulateQ
        (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
        (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
          forgery.signature)).run initial
      pure ((forgery, verified.1),
        firstLaneAppendVerificationState right.1.1.secretKey forgery initial
          verified.2)
  have hfullBound : Budget (adversary.main left.publicKey) countLimit sourceInitial := by
    unfold Budget finish
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    exact hsourceBound
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    (cappedBothTracedMappedAdversaryImpl left.publicKey secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    leftFinish rightFinish directHashActionCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun state spent => state.2.hashInputs.length = spent) Budget
    (by
      intro input next remaining state result hrest hresult
      unfold Budget at hrest ⊢
      rw [simulateQ_query_bind, bind_assoc] at hrest
      have hr : (result.1, result.2.1.1.1) ∈ support
          ((simulateQ romImpl (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey input)).run state.1.1.1) := by
        rw [← cappedBothTracedMappedAdversaryImpl_cache_projection, support_map]
        exact ⟨result, hresult, rfl⟩
      exact sourceUnloggedMappedAdversaryImpl_consistent_query_bound left.publicKey secretKey input
        (fun response => simulateQ (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey)
          (next ((OracleSpec.query input).cont response)) >>= finish) state.1.1.1 remaining hrest _ hr)
    (by
      intro spent input state firstState history hstates hprefix hacct
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2.1, by
          rw [hgood.2.2.2, hacct]⟩
      · exact Or.inr hhit)
    countLimit hitLimit
    (by
      intro forgery spent remaining state firstState history hremaining
        hstates hcount hacct htotal
      unfold Budget finish at hremaining
      simp only [simulateQ_pure, pure_bind] at hremaining
      have hverifyBound :
          HashQueryBound (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
            forgery.signature) state.1.1.1 remaining :=
        (hashQueryBound_map_iff _ _ _ _).mp hremaining
      have hverifier :=
        relTriple_sourceExact_firstLane_verifier_boundedHit countLimit hitLimit
          spent remaining left right hrel hleftSupport hrightSupport
            (Concrete.scheme.verify left.publicKey forgery.epoch
              forgery.message forgery.signature) state hverifyBound firstState
                history hstates hcount htotal hlimits
      let sourceFinish := fun verified : Bool × SourceExactTracedState =>
        ((forgery, verified.1),
          sourceAppendVerificationState secretKey forgery state verified.2)
      let firstFinish := fun verified :
          ((Bool × GlobalHighDirectTracedState) ×
            FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (((forgery, verified.1.1),
          firstLaneAppendVerificationState right.1.1.secretKey forgery
            firstState verified.1.2), verified.2)
      have hlifted : RelTriple
          (sourceFinish <$>
            (simulateQ sourceExactTracedVerifierImpl
              (Concrete.scheme.verify left.publicKey forgery.epoch
                forgery.message forgery.signature)).run state)
          (firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.epoch
                  forgery.message forgery.signature)).run firstState)).run)
          (fun leftResult firstResult =>
            (leftResult.1 = firstResult.1.1 ∧
              SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
                firstResult.1.2 (history ++ firstResult.2) ∧
              FirstLaneOracleSimulation.hazardCount
                (history ++ firstResult.2) ≤ countLimit) ∨
            FirstLaneOracleSimulation.CombinedHit right.1.2
              (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                (history ++ firstResult.2))) := by
        apply relTriple_map
        apply relTriple_post_mono (relTriple_with_support hverifier)
        intro leftVerified firstVerified hvertified
        obtain ⟨hverifiedRelation, hleftVerifiedSupport,
          hfirstVerifiedSupport⟩ := hvertified
        rcases hverifiedRelation with hgood | hhit
        · exact Or.inl ⟨congrArg (Prod.mk forgery) hgood.1,
            SourceFirstLaneExactGoodStateRelation.appendVerification left right
              hrel hleftSupport hrightSupport forgery state leftVerified.2
                firstState firstVerified.1.2 history
                  (history ++ firstVerified.2) hstates hgood.2.1 (by
                    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
                    have hpublicKey : left.publicKey =
                        right.1.1.publicKey := hrel.1.toStable.1.2.1
                    rw [hpublicKey] at hfirstVerifiedSupport
                    have hlocal :=
                      globalFirstLaneExactTracedVerifier_append_trace_sublist
                        right.1.2 right.1.1 right.2 forgery firstState
                          leftVerified.2.1.2
                          (by
                            have hkeyResult :=
                              trajectoryProgrammedGlobalChainKeygen_support_keyResult
                                right.1.1 hrightSupport
                            exact keygen_parameter_eq right.1.1.keyResult
                              hkeyResult)
                          firstVerified hfirstVerifiedSupport
                    have hleftEncoding : leftVerified.2.1.2 = state.1.2 := by
                      rw [sourceExactTracedVerifierImpl_run_eq, support_map]
                        at hleftVerifiedSupport
                      obtain ⟨baseResult, _hbase, heq⟩ := hleftVerifiedSupport
                      subst leftVerified
                      rfl
                    have hencodingInitial := hstates.2.1
                    have hencodingFinal : List.Sublist leftVerified.2.1.2
                        history.encodingActions := by
                      rw [hleftEncoding]
                      exact hencodingInitial
                    exact hlocal.trans
                      (hencodingFinal.append (List.Sublist.refl _))),
            hgood.2.2⟩
        · exact Or.inr hhit
      have hsource : leftFinish forgery state = sourceFinish <$>
          (simulateQ sourceExactTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey forgery.epoch
              forgery.message forgery.signature)).run state := by
        unfold leftFinish
        rw [sourceExactTracedVerifierImpl_run_eq]
        simp [sourceFinish, sourceAppendVerificationState, Functor.map_map]
      have hright :
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            (rightFinish forgery firstState)).run =
          firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.epoch
                  forgery.message forgery.signature)).run firstState)).run := by
        unfold rightFinish
        rw [simulateQ_bind, WriterT.run_bind']
        simp [firstFinish, firstLaneAppendVerificationState]
      rw [hsource, hright]
      exact hlifted)
    0 countLimit (adversary.main left.publicKey) sourceInitial
      firstLaneInitial hfullBound [] hinitial
      (by simp [FirstLaneOracleSimulation.hazardCount]) (by rfl) (by omega)
        hlimits
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalFirstLaneExactTracedDetailedExecution
  simp only [StateT.run_mk]
  rw [← hpublicKey]
  exact hcoupling

set_option maxRecDepth 1000000

abbrev GlobalFirstLaneExactCoupledProgramResult :=
  (((ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) ×
    (((Forgery × Bool) × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex))

noncomputable def globalFirstLaneExactCoupledProgram
    (adversary : Adversary) :
    ProbComp GlobalFirstLaneExactCoupledProgramResult := do
  let right ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← (simulateQ
    (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
    ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
      right.2).run (GlobalHighDirectTracedState.initial
        (globalFilteredCausalKeygenState right.1.1)))).run
  pure (right, execution)

def SourceFirstLaneExactBoundedProgramRelation
    (countLimit hitLimit : Nat)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2 ∧
      FirstLaneOracleSimulation.hazardCount right.2.2 ≤ countLimit) ∨
    FirstLaneOracleSimulation.CombinedHit right.1.1.2
      (FirstLaneOracleSimulation.enforceHazardTrace hitLimit right.2.2))

theorem relTriple_sourceGlobalExact_firstLane_program_boundedHit_sub_keygen
    (q hitLimit : Nat)
    (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hlimits : q - treeHashQueryCount treeHeight ≤ hitLimit) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (globalFirstLaneExactCoupledProgram adversary)
      (SourceFirstLaneExactBoundedProgramRelation
        (q - treeHashQueryCount treeHeight) hitLimit) := by
  unfold sourceGlobalExactTracedProgram globalFirstLaneExactCoupledProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  have hleftKeyResult :=
    trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport
  have hmaterializedKeyResult :
      Concrete.materializeCachedKeyResult left.keyResult ∈ support
        ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
    exact Concrete.oldKeygen_support_materializedPrecomputedKeygen
      left.keyResult hleftKeyResult
  have hsourceBound :=
    sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
      q adversary hbound (Concrete.materializeCachedKeyResult left.keyResult)
        hmaterializedKeyResult
  apply relTriple_bind
    (relTriple_sourceExact_firstLane_detailedExecution_boundedHit
      (q - treeHashQueryCount treeHeight) hitLimit adversary left right hrel
        hleftSupport hrightViewSupport hsourceBound hlimits)
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution⟩

def globalFirstLaneExactCoupledProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2), result.2.1), result.2.2))

noncomputable def globalFirstLaneExactCoupledContinuation
    (adversary : Adversary)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp GlobalFirstLaneExactPublicEagerResult := do
  let keyResult ← globalHighDirectKeygenAfterParameter parameter
  let execution ← (simulateQ
    (FirstLaneOracleSimulation.eagerTraceImpl base)
    ((globalFirstLaneExactTracedDetailedExecution adversary keyResult.1
      keyResult.2).run (GlobalHighDirectTracedState.initial
        (globalFilteredCausalKeygenState keyResult.1)))).run
  pure (base, ((keyResult, execution.1), execution.2))

theorem globalFirstLaneExactCoupledProgram_projection_eq_parameterFirst
    (adversary : Adversary) :
    globalFirstLaneExactCoupledProjection <$>
      globalFirstLaneExactCoupledProgram adversary = (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalFirstLaneExactCoupledContinuation adversary parameter base) := by
  unfold globalFirstLaneExactCoupledProgram
  rw [coupledGlobalChainKeygenWithBaseHighFull_eq_direct]
  simp [globalFirstLaneExactCoupledProjection,
    globalFirstLaneExactCoupledContinuation, bind_assoc]

theorem firstLane_eagerTrace_liftProbComp_then_bind
    (base : GlobalChainValueIndex → Digest)
    (keygen : ProbComp κ)
    (body : κ → OracleComp GlobalFirstLaneWorld α) :
    (do
      let keyResult ← keygen
      let execution ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base)
        (body keyResult)).run
      pure (base, ((keyResult, execution.1), execution.2))) = (do
      let result ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base) (do
          let keyResult ← FirstLaneOracleSimulation.liftProbComp keygen
          let execution ← body keyResult
          pure (keyResult, execution))).run
      pure (base, result)) := by
  simp only [simulateQ_bind, WriterT.run_bind', bind_assoc]
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [simulateQ_pure, WriterT.run_pure]

theorem globalFirstLaneExactCoupledContinuation_eq_eagerAfterBase
    (adversary : Adversary)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let parameter ← Concrete.samplePublicParameter
      globalFirstLaneExactCoupledContinuation adversary parameter base) = (do
      let result ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base)
        (globalFirstLaneExactTracedProgram adversary)).run
      pure (base, result)) := by
  unfold globalFirstLaneExactCoupledContinuation
    globalFirstLaneExactTracedProgram globalHighDirectKeygen
  simpa only [bind_assoc] using
    (firstLane_eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectKeygenAfterParameter parameter)
      (fun keyResult =>
        (globalFirstLaneExactTracedDetailedExecution adversary keyResult.1
          keyResult.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState keyResult.1))))

theorem evalDist_globalFirstLaneExactCoupledProjection_eq_eagerExperiment
    (adversary : Adversary) :
    evalDist (globalFirstLaneExactCoupledProjection <$>
      globalFirstLaneExactCoupledProgram adversary) =
    evalDist (FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedProgram adversary)) := by
  rw [globalFirstLaneExactCoupledProgram_projection_eq_parameterFirst]
  calc
    evalDist (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalFirstLaneExactCoupledContinuation adversary parameter base) =
      evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Concrete.samplePublicParameter
        globalFirstLaneExactCoupledContinuation adversary parameter base) := by
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            Concrete.samplePublicParameter independentGlobalChainValueTable _
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let result ← (simulateQ
          (FirstLaneOracleSimulation.eagerTraceImpl base)
          (globalFirstLaneExactTracedProgram adversary)).run
        pure (base, result)) := by
          rw [evalDist_bind, evalDist_bind]
          apply bind_congr
          intro base
          exact congrArg evalDist
            (globalFirstLaneExactCoupledContinuation_eq_eagerAfterBase
              adversary base)
    _ = _ := by
      unfold FirstLaneOracleSimulation.eagerExperiment
      rw [evalDist_bind, evalDist_bind]
      unfold independentGlobalChainValueTable
        RevealProbeOracleSimulation.eagerTableSample
      rfl


set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def liftGlobalChainTrace
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex :=
  trace.map FirstLaneOracleSimulation.ObservedAction.chain

@[simp]
theorem liftGlobalChainTrace_chainActions
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (liftGlobalChainTrace trace).chainActions = trace := by
  simp [liftGlobalChainTrace,
    FirstLaneOracleSimulation.ActionTrace.chainActions]

@[simp]
theorem liftGlobalChainTrace_hazardCount
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (liftGlobalChainTrace trace) =
      RevealProbeOracleSimulation.observedProbeCount trace := by
  induction trace with
  | nil => simp [liftGlobalChainTrace,
      FirstLaneOracleSimulation.hazardCount,
      RevealProbeOracleSimulation.observedProbeCount]
  | cons action trace ih =>
      cases action with
      | probe index target =>
          simp only [liftGlobalChainTrace, List.map_cons,
            FirstLaneOracleSimulation.hazardCount,
            RevealProbeOracleSimulation.observedProbeCount,
            Nat.succ.injEq]
          change FirstLaneOracleSimulation.hazardCount
              (liftGlobalChainTrace trace) =
            RevealProbeOracleSimulation.observedProbeCount trace
          exact ih
      | reveal index value =>
          simp only [liftGlobalChainTrace, List.map_cons,
            FirstLaneOracleSimulation.hazardCount,
            RevealProbeOracleSimulation.observedProbeCount]
          change FirstLaneOracleSimulation.hazardCount
              (liftGlobalChainTrace trace) =
            RevealProbeOracleSimulation.observedProbeCount trace
          exact ih

theorem simulate_eagerTrace_lift_emitObservedTrace
    (table : GlobalChainValueIndex → Digest)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hagrees : RevealProbeOracleSimulation.TraceAgrees table trace) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (globalFirstLaneLiftRevealProbe
        (RevealProbeOracleSimulation.emitObservedTrace trace))).run =
      pure ((), liftGlobalChainTrace trace) := by
  induction trace with
  | nil =>
      simp [RevealProbeOracleSimulation.emitObservedTrace,
        globalFirstLaneLiftRevealProbe, liftGlobalChainTrace]
  | cons action trace ih =>
      cases action with
      | probe index target =>
          simp only [RevealProbeOracleSimulation.TraceAgrees] at hagrees
          simp [RevealProbeOracleSimulation.emitObservedTrace,
            RevealProbeOracleSimulation.probeQuery,
            globalFirstLaneLiftRevealProbe, globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.probeQuery, simulateQ_bind,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            liftGlobalChainTrace]
          change (fun x => (x.1,
              FirstLaneOracleSimulation.ObservedAction.chain
                (.probe index target) :: x.2)) <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  (RevealProbeOracleSimulation.emitObservedTrace trace)
                )).run = _
          rw [ih hagrees]
          rfl
      | reveal index value =>
          obtain ⟨hvalue, hrest⟩ := hagrees
          simp [RevealProbeOracleSimulation.emitObservedTrace,
            RevealProbeOracleSimulation.revealQuery,
            globalFirstLaneLiftRevealProbe, globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.revealQuery, simulateQ_bind,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, hvalue,
            liftGlobalChainTrace]
          change (fun x => (x.1,
              FirstLaneOracleSimulation.ObservedAction.chain
                (.reveal index value) :: x.2)) <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  (RevealProbeOracleSimulation.emitObservedTrace trace)
                )).run = _
          rw [ih hrest]
          rfl

noncomputable def appendGlobalFirstLaneExactPublicTrace
    (result : GlobalFirstLaneExactPublicEagerResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  (result.1, (result.2.1, result.2.2 ++ liftGlobalChainTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace result.2.1)))

theorem simulate_eagerTrace_bind_lift_emitObservedTrace_keep
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α)
    (suffix : α →
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hagrees : ∀ result, RevealProbeOracleSimulation.TraceAgrees table
      (suffix result)) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (do
      let result ← computation
      let _ ← globalFirstLaneLiftRevealProbe
        (RevealProbeOracleSimulation.emitObservedTrace (suffix result))
      pure result)).run =
    (fun result =>
      (result.1, result.2 ++ liftGlobalChainTrace (suffix result.1))) <$>
      (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        computation).run := by
  rw [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨result, trace⟩
  simp only [Function.comp_apply]
  rw [simulateQ_bind, WriterT.run_bind']
  rw [simulate_eagerTrace_lift_emitObservedTrace table (suffix result)
    (hagrees result)]
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, pure_bind,
    Prod.map_apply, id_eq]
  change (pure (result,
      trace ++ (liftGlobalChainTrace (suffix result) ++ [])) : ProbComp _) =
    pure (result, trace ++ liftGlobalChainTrace (suffix result))
  rw [List.append_nil]

theorem eagerExperiment_globalFirstLaneExactTracedPublicProgram_eq_append
    (adversary : Adversary) :
    FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedPublicProgram adversary) =
    appendGlobalFirstLaneExactPublicTrace <$>
      FirstLaneOracleSimulation.eagerExperiment
        (globalFirstLaneExactTracedProgram adversary) := by
  unfold globalFirstLaneExactTracedPublicProgram
    FirstLaneOracleSimulation.eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_bind_lift_emitObservedTrace_keep table
    (globalFirstLaneExactTracedProgram adversary)
    globalHighDirectExactForgeryPrimaryProbeTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace_agrees table)]
  simp [appendGlobalFirstLaneExactPublicTrace, map_eq_bind_pure_comp,
    bind_assoc]

theorem globalFirstLaneExactCoupledProgram_support_info
    (adversary : Adversary)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    result.1 ∈ support coupledGlobalChainKeygenWithBaseHighFull ∧
    result.2 ∈ support
      ((simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary result.1.1.1
          result.1.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState result.1.1.1)))).run) := by
  unfold globalFirstLaneExactCoupledProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨right, hright, htail⟩ := hresult
  rw [mem_support_bind_iff] at htail
  obtain ⟨execution, hexecution, hpure⟩ := htail
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact ⟨hright, hexecution⟩

theorem exists_globalHighMonitored_of_coupled_support
    (adversary : Adversary)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    ∃ highResult ∈ support (globalHighMonitoredProgram adversary),
      globalHighMonitoredFullProjection highResult =
        (result.1.1.2,
          (((result.1.1.1, result.1.2), result.2.1),
            result.2.2.chainActions)) := by
  obtain ⟨hkey, hexecution⟩ :=
    globalFirstLaneExactCoupledProgram_support_info adversary result hresult
  have hmapped : (result.2.1, result.2.2.chainActions) ∈ support
      ((fun execution => (execution.1, execution.2.chainActions)) <$>
        (simulateQ
          (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
          ((globalFirstLaneExactTracedDetailedExecution adversary
            result.1.1.1 result.1.2).run (GlobalHighDirectTracedState.initial
              (globalFilteredCausalKeygenState result.1.1.1)))).run) := by
    rw [support_map]
    exact ⟨result.2, hexecution, rfl⟩
  rw [simulate_globalFirstLaneEagerTrace_chainProjection] at hmapped
  rw [globalFirstLaneErase_exactTracedDetailedExecution adversary
    result.1.1.1 result.1.2 (GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState result.1.1.1))] at hmapped
  rw [← map_globalHighMonitoredDetailedExecution_full_projection]
    at hmapped
  rw [support_map] at hmapped
  obtain ⟨highExecution, hhighExecution, hprojection⟩ := hmapped
  let highResult : GlobalHighMonitoredProgramResult :=
    (result.1, highExecution)
  have hhighResult : highResult ∈ support
      (globalHighMonitoredProgram adversary) := by
    unfold globalHighMonitoredProgram
    rw [mem_support_bind_iff]
    refine ⟨result.1, hkey, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨highExecution, hhighExecution, by simp [highResult]⟩
  refine ⟨highResult, hhighResult, ?_⟩
  simpa [highResult, globalHighMonitoredFullProjection] using
    congrArg (fun execution =>
      (result.1.1.2,
        (((result.1.1.1, result.1.2), execution.1), execution.2)))
      hprojection

theorem sourceFirstLaneExactGood_to_globalHighRelation
    (adversary : Adversary)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2) :
    ∃ highResult ∈ support (globalHighMonitoredProgram adversary),
      SourceGlobalHighMonitoredProgramRelation
        (sourceGlobalExactErasedResult left)
        highResult ∧
      globalHighMonitoredFullProjection highResult =
        (right.1.1.2,
          (((right.1.1.1, right.1.2), right.2.1),
            right.2.2.chainActions)) ∧
      List.Sublist left.2.2.1.2 right.2.2.encodingActions ∧
      List.Sublist
        (CappedEncodingMonitor.validObservedSignEpochs
          right.2.2.encodingActions)
        (left.2.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
  obtain ⟨highResult, hhighSupport, hprojection⟩ :=
    exists_globalHighMonitored_of_coupled_support adversary right
      hrightSupport
  let witness := globalStateOfFirstLane right.2.1.2 right.2.2
  have hwitnessRelation : GlobalSigningMonitoredTracedStateRelation left.1
      right.1.1 (sourceExactSigningProjection left.2.2) witness := hgood.2.1
  have hwitnessEncoding := hgood.2.2.1
  have hwitnessValidEpochs := hgood.2.2.2
  have hbase : highResult.1.1.2 = right.1.1.2 :=
    congrArg Prod.fst hprojection
  have hdirect :
      ((highResult.1.1.1, highResult.1.2),
        (highResult.2.1, GlobalHighDirectTracedState.mk
          highResult.2.2.1.causal highResult.2.2.2)) =
      ((right.1.1.1, right.1.2),
        (right.2.1.1, right.2.1.2)) :=
    congrArg (fun projected => projected.2.1) hprojection
  have hchain : highResult.2.2.1.trace = right.2.2.chainActions :=
    congrArg (fun projected => projected.2.2) hprojection
  have hkeyView : highResult.1.1.1 = right.1.1.1 :=
    congrArg (fun direct => direct.1.1) hdirect
  have hedgeHigh : highResult.1.2 = right.1.2 :=
    congrArg (fun direct => direct.1.2) hdirect
  have houtcome : highResult.2.1 = right.2.1.1 :=
    congrArg (fun direct => direct.2.1) hdirect
  have hstateProjection :
      GlobalHighDirectTracedState.mk highResult.2.2.1.causal highResult.2.2.2 =
        right.2.1.2 :=
    congrArg (fun direct => direct.2.2) hdirect
  have hfullKey : highResult.1 = right.1 := by
    apply Prod.ext
    · apply Prod.ext
      · exact hkeyView
      · exact hbase
    · exact hedgeHigh
  have hstate : highResult.2.2 = witness := by
    exact (globalStateOfFirstLane_eq highResult.2.2 right.2.1.2 right.2.2
      hstateProjection.symm hchain.symm).symm
  refine ⟨highResult, hhighSupport, ?_, hprojection, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ProgrammedGlobalChainKeygenBaseHighStableRelation left.1
        highResult.1
      rw [hfullKey]
      exact hkey
    · apply Or.inl
      constructor
      · change left.2.1 = highResult.2.1
        exact hgood.1.trans houtcome.symm
      · simpa [sourceGlobalExactErasedResult, sourceGlobalExactErasedExecution,
          GlobalSigningMonitoredTracedStateRelation,
          sourceExactSigningProjection, sourceSigningTracedStateProjection] using
            (show GlobalSigningMonitoredTracedStateRelation left.1
              highResult.1.1
              (sourceExactSigningProjection left.2.2) highResult.2.2 by
                rw [hfullKey, hstate]
                exact hwitnessRelation)
  · exact hwitnessEncoding
  · have hattacker : left.2.2.2 = witness.2 := by
      simpa [GlobalSigningMonitoredTracedStateRelation,
        sourceExactSigningProjection, sourceSigningTracedStateProjection] using
          hwitnessRelation.2
    rw [hattacker]
    exact hwitnessValidEpochs

theorem sourceWinningExactFirstLane_good_implies_public_combinedHit
    (adversary : Adversary)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    FirstLaneOracleSimulation.CombinedHit
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).1
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).2.2 := by
  obtain ⟨highResult, hhighSupport, hhighRelation, hprojection,
    hencodingSub, hvalidSub⟩ :=
    sourceFirstLaneExactGood_to_globalHighRelation adversary left right
      hrightSupport hkey hgood
  let both := sourceGlobalExactProgramResult left
  have hbothMapped : both ∈ support
      (sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary) := by
    rw [support_map]
    exact ⟨left, hleftSupport, rfl⟩
  have hboth : both ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary) :=
    (mem_support_iff_of_evalDist_eq
      (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary) both).mp
        hbothMapped
  have hencodingSupport : cappedBothEncodingProjection both ∈ support
      (cappedDetailedGameWithEncodingTrace adversary) := by
    rw [← cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq,
      support_map]
    exact ⟨both, hboth, rfl⟩
  unfold SourceWinningExactFirstLaneEvent at hevent
  unfold WinningExactFirstLaneBadEventOccurs at hevent
  rcases hevent with hencoding | hchain
  · have hhit := cappedExactEncodingBranch_implies_monitorHit adversary
      (cappedBothEncodingProjection both) hencodingSupport hencoding
    have hbothExecution :=
      cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
        adversary both hboth
    have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
      adversary both.1.1.1 both.1.1.2 both.1.2 both.2 hbothExecution
    have hvalidBoth : SigningTranscript.Valid
        both.2.2.2.toSigningLog := by
      rw [← hlogs]
      exact hencoding.1.signingTranscript_valid
    have hvalidLeft : SigningTranscript.Valid
        left.2.2.2.toSigningLog := by
      simpa [both, sourceGlobalExactProgramResult,
        sourceGlobalExactExecutionResult] using hvalidBoth
    apply globalHighExactEncodingEvent_implies_combinedHit
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).1
      left.2.2.1.2 left.2.2.2
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).2.2
    · simpa [appendGlobalFirstLaneExactPublicTrace,
        globalFirstLaneExactCoupledProjection, liftGlobalChainTrace,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        FirstLaneOracleSimulation.ActionTrace.encodingActions_append] using
          hencodingSub
    · simpa [appendGlobalFirstLaneExactPublicTrace,
        globalFirstLaneExactCoupledProjection, liftGlobalChainTrace,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        FirstLaneOracleSimulation.ActionTrace.encodingActions_append] using
          hvalidSub
    · exact hvalidLeft
    · simpa [both, cappedBothEncodingProjection,
        sourceGlobalExactProgramResult, sourceGlobalExactExecutionResult] using
          hhit
  · obtain ⟨chain, hwinning, hrevealed⟩ := hchain
    have hkeygen := cappedBothTraceGameResult_keyResult_mem_support
      adversary both hboth
    have hafter := cappedBothTraceGameResult_cacheExecution_mem_support
      adversary both hboth
    have horiginChain := chainValueRevealed_afterKeygen_has_origin adversary
      both.1 hkeygen (both.2.1, both.2.2.1.1.1) hafter chain hrevealed
    let leftOld := sourceGlobalExactErasedResult left
    let rightOld := highResult
    have hleftOld : leftOld ∈ support
        (sourceGlobalTracedProgram adversary) :=
      sourceGlobalExactErasedResult_mem_support adversary hleftSupport
    have hrightOld : rightOld ∈ support
        (globalHighMonitoredProgram adversary) :=
      hhighSupport
    have houtcome :=
      cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
        adversary both hboth
    have hwinningAction : WinningOutcomeBadEventOccurs
        (cappedBothActionProjection both).1.2.2
        (cappedBothActionProjection both).1.2.1 (.chain chain) := by
      rw [← houtcome]
      exact hwinning
    have horiginAction : OutcomeChainValueHasKeygenOrigin
        both.1.2 (cappedBothActionProjection both).1.2.2
        both.1.1.2 (cappedBothActionProjection both).1.2.1 chain := by
      rw [← houtcome]
      exact horiginChain
    have horiginOld : GlobalWinningOutcomeChainValueHasKeygenOrigin
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.2.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.2.1 := by
      refine ⟨chain, ?_, ?_⟩
      · simpa [leftOld, both, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
          sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
          cappedBothActionProjection, sourceGlobalExactProgramResult,
          sourceGlobalExactExecutionResult,
          ProgrammedGlobalChainKeygenView.keyResult,
          Concrete.materializeCachedKeyResult, Prod.eta] using hwinningAction
      · simpa [leftOld, both, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
          sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
          cappedBothActionProjection, sourceGlobalExactProgramResult,
          sourceGlobalExactExecutionResult,
          ProgrammedGlobalChainKeygenView.keyResult,
          Concrete.materializeCachedKeyResult, Prod.eta] using horiginAction
    have hobserved := sourceGlobal_origin_implies_right_publicObservedHit
      adversary leftOld rightOld hleftOld hrightOld hhighRelation horiginOld
    apply Or.inr
    unfold RevealProbeOracleSimulation.ObservedHit at hobserved
    have hpublic := globalHighMonitored_fullProjection_public_eq highResult
    rw [← hpublic, hprojection] at hobserved
    simpa [appendGlobalHighDirectExactPublicTrace,
      appendGlobalFirstLaneExactPublicTrace,
      globalFirstLaneExactCoupledProjection,
      FirstLaneOracleSimulation.ActionTrace.chainActions_append] using hobserved

theorem observedProbeCount_exactForgeryPrimaryProbeTrace
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.observedProbeCount
      (globalHighDirectExactForgeryPrimaryProbeTrace result) = numChains := by
  unfold globalHighDirectExactForgeryPrimaryProbeTrace
  exact observedProbeCount_globalHighDirectForgeryPrimaryProbeTrace _

theorem hazardCount_appendGlobalFirstLaneExactPublicTrace
    (result : GlobalFirstLaneExactPublicEagerResult) :
    FirstLaneOracleSimulation.hazardCount
      (appendGlobalFirstLaneExactPublicTrace result).2.2 =
    FirstLaneOracleSimulation.hazardCount result.2.2 + numChains := by
  simp [appendGlobalFirstLaneExactPublicTrace,
    FirstLaneOracleSimulation.hazardCount_append,
    observedProbeCount_exactForgeryPrimaryProbeTrace]

noncomputable def globalFirstLaneExactCoupledPublicProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  appendGlobalFirstLaneExactPublicTrace
    (globalFirstLaneExactCoupledProjection result)

def GlobalFirstLaneExactCoupledEnforcedHit
    (fuel : Nat) (result : GlobalFirstLaneExactCoupledProgramResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit
    (globalFirstLaneExactCoupledPublicProjection result).1
    (FirstLaneOracleSimulation.enforceHazardTrace fuel
      (globalFirstLaneExactCoupledPublicProjection result).2.2)

theorem sourceWinningExactFirstLane_good_implies_public_enforcedHit
    (countLimit fuel : Nat)
    (adversary : Adversary)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2 ∧
      FirstLaneOracleSimulation.hazardCount right.2.2 ≤ countLimit)
    (hfuel : countLimit + numChains ≤ fuel)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    GlobalFirstLaneExactCoupledEnforcedHit fuel right := by
  have hraw :=
    sourceWinningExactFirstLane_good_implies_public_combinedHit adversary
      left right hleftSupport hrightSupport hkey ⟨hgood.1, hgood.2.1⟩ hevent
  have hcount : FirstLaneOracleSimulation.hazardCount
      (globalFirstLaneExactCoupledPublicProjection right).2.2 ≤ fuel := by
    rw [globalFirstLaneExactCoupledPublicProjection,
      hazardCount_appendGlobalFirstLaneExactPublicTrace]
    dsimp only [globalFirstLaneExactCoupledProjection]
    omega
  unfold GlobalFirstLaneExactCoupledEnforcedHit
  rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
    _ _ hcount]
  exact hraw

theorem sourceWinningExactFirstLane_hit_implies_public_enforcedHit
    (fuel : Nat)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hhit : FirstLaneOracleSimulation.CombinedHit right.1.1.2
      (FirstLaneOracleSimulation.enforceHazardTrace fuel right.2.2)) :
    GlobalFirstLaneExactCoupledEnforcedHit fuel right := by
  unfold GlobalFirstLaneExactCoupledEnforcedHit
    globalFirstLaneExactCoupledPublicProjection
    appendGlobalFirstLaneExactPublicTrace
    globalFirstLaneExactCoupledProjection
  exact FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
    right.1.1.2 fuel right.2.2
      (liftGlobalChainTrace
        (globalHighDirectExactForgeryPrimaryProbeTrace
          ((right.1.1.1, right.1.2), right.2.1))) hhit

theorem sourceWinningExactFirstLane_implies_coupled_enforcedHit
    (countLimit fuel : Nat)
    (adversary : Adversary)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hrelation : SourceFirstLaneExactBoundedProgramRelation
      countLimit fuel left right)
    (hfuel : countLimit + numChains ≤ fuel)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    GlobalFirstLaneExactCoupledEnforcedHit fuel right := by
  rcases hrelation with ⟨hkey, hgood | hhit⟩
  · exact sourceWinningExactFirstLane_good_implies_public_enforcedHit
      countLimit fuel adversary left right hleftSupport hrightSupport hkey
        hgood hfuel hevent
  · exact sourceWinningExactFirstLane_hit_implies_public_enforcedHit
      fuel right hhit

theorem evalDist_globalFirstLaneExactCoupledPublicProjection_eq_eager
    (adversary : Adversary) :
    evalDist (globalFirstLaneExactCoupledPublicProjection <$>
      globalFirstLaneExactCoupledProgram adversary) =
    evalDist (globalFirstLaneExactPublicEagerExperiment adversary) := by
  calc
    evalDist (globalFirstLaneExactCoupledPublicProjection <$>
        globalFirstLaneExactCoupledProgram adversary) =
      evalDist (appendGlobalFirstLaneExactPublicTrace <$>
        (globalFirstLaneExactCoupledProjection <$>
          globalFirstLaneExactCoupledProgram adversary)) := by
            apply congrArg evalDist
            rw [Functor.map_map]
            rfl
    _ = evalDist (appendGlobalFirstLaneExactPublicTrace <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary)) := by
      exact evalDist_map_congr_of_evalDist_eq
        appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection <$>
          globalFirstLaneExactCoupledProgram adversary)
        (FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary))
        (evalDist_globalFirstLaneExactCoupledProjection_eq_eagerExperiment
          adversary)
    _ = _ := by
      unfold globalFirstLaneExactPublicEagerExperiment
      rw [eagerExperiment_globalFirstLaneExactTracedPublicProgram_eq_append]

def GlobalFirstLaneExactPublicEnforcedHit
    (fuel : Nat) (result : GlobalFirstLaneExactPublicEagerResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit result.1
    (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2)

theorem sourceWinningExactFirstLane_probability_le_coupled_enforcedHit
    (q fuel : Nat)
    (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hfuel : q - treeHashQueryCount treeHeight + numChains ≤ fuel) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobalExact_firstLane_program_boundedHit_sub_keygen
        q fuel adversary hbound (by omega)))
  intro left right hrelation hevent
  exact sourceWinningExactFirstLane_implies_coupled_enforcedHit
    (q - treeHashQueryCount treeHeight) fuel adversary left right
      hrelation.2.1 hrelation.2.2 hrelation.1 hfuel hevent

theorem coupled_enforcedHit_probability_eq_public_eager
    (fuel : Nat) (adversary : Adversary) :
    Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] =
      Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] := by
  calc
    _ = Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactCoupledPublicProjection <$>
          globalFirstLaneExactCoupledProgram adversary] := by
      rw [probEvent_map]
      rfl
    _ = _ := probEvent_eq_of_evalDist_eq _
      (evalDist_globalFirstLaneExactCoupledPublicProjection_eq_eager
        adversary)

theorem public_eager_enforcedHit_probability_le
    (fuel : Nat) (adversary : Adversary) :
    Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ = Pr[FirstLaneOracleSimulation.ExperimentHit |
        FirstLaneOracleSimulation.enforceEagerResult fuel <$>
          FirstLaneOracleSimulation.eagerExperiment
            (globalFirstLaneExactTracedPublicProgram adversary)] := by
      unfold GlobalFirstLaneExactPublicEnforcedHit
        globalFirstLaneExactPublicEagerExperiment
      rw [probEvent_map]
      rfl
    _ = Pr[FirstLaneOracleSimulation.ExperimentHit |
        FirstLaneOracleSimulation.eagerExperiment
          (FirstLaneOracleSimulation.enforceHazardBound fuel
            (globalFirstLaneExactTracedPublicProgram adversary))] := by
      rw [FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map]
    _ = Pr[(fun hit : Bool => hit = true) |
        FirstLaneOracleSimulation.structuralExperiment
          (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty fuel
          (FirstLaneOracleSimulation.enforceHazardBound fuel
            (globalFirstLaneExactTracedPublicProgram adversary))] := by
      exact FirstLaneOracleSimulation.combinedHit_probability_eq_structuralExperiment
        fuel (FirstLaneOracleSimulation.enforceHazardBound fuel
          (globalFirstLaneExactTracedPublicProgram adversary))
          (FirstLaneOracleSimulation.enforceHazardBound_isHazardQueryBoundP
            fuel (globalFirstLaneExactTracedPublicProgram adversary))
    _ ≤ _ := FirstLaneOracleSimulation.structuralExperiment_empty_true_probability_le
      fuel (FirstLaneOracleSimulation.enforceHazardBound fuel
        (globalFirstLaneExactTracedPublicProgram adversary))

theorem sourceWinningExactFirstLane_probability_le
    (q : Nat)
    (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      ((q - treeHashQueryCount treeHeight + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  let fuel := q - treeHashQueryCount treeHeight + numChains
  calc
    _ ≤ Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] :=
      sourceWinningExactFirstLane_probability_le_coupled_enforcedHit q fuel
        adversary hbound (by simp [fuel])
    _ = Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] :=
      coupled_enforcedHit_probability_eq_public_eager fuel adversary
    _ ≤ _ := public_eager_enforcedHit_probability_le fuel adversary

theorem hasExactFirstLaneBound_of_hashQueryBound
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    HasExactFirstLaneBound q adversary := by
  unfold HasExactFirstLaneBound
  rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
  exact sourceWinningExactFirstLane_probability_le q adversary hbound

theorem hasExactFirstLaneBounds : HasExactFirstLaneBounds := by
  intro q adversary hbound
  exact hasExactFirstLaneBound_of_hashQueryBound q adversary hbound

end XmssSecurity.CappedChain
