import XmssSecurity.Proof.CappedGlobalChainHighReplay
import XmssSecurity.Proof.CappedGlobalCausalUniformTrace
import XmssSecurity.Proof.CappedChain.SourceDirectTrace
import XmssSecurity.Proof.CappedChain.ReturnedChainValueCoverage
import XmssSecurity.Proof.EncodingHashCacheReplay
import XmssSecurity.Proof.RunObservedAppend

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem relTriple_programmed_monitoredGlobalUniformQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right leftCache
      rightState)
    (n : Nat) :
    RelTriple
      ((fun output : Fin (n + 1) => (output, leftCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      ((monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalUniformImpl n).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · rw [simulate_eagerTrace_globalCausalUniformImpl]
    have hmapped : RelTriple
        ((fun output : Fin (n + 1) => (output, leftCache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        ((fun output : Fin (n + 1) =>
          ((output, rightState.causal),
            ([] : RevealProbeOracleSimulation.ActionTrace
              GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1.1 ∧
            GlobalFilteredCausalStateRelation left right leftResult.2
              rightResult.1.2) := by
      apply relTriple_map
      apply relTriple_post_mono
        (relTriple_refl
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact ⟨rfl, hcausal⟩
    apply relTriple_post_mono hmapped
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨by trivial, ReplaysCausalReveals.nil rightState.causal.revealed⟩
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact hretained

abbrev GlobalMonitoredTracedState :=
  GlobalMonitoredCausalState × AttackerActionTrace

def GlobalMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState) : Prop :=
  GlobalMonitoredFilteredStateRelation left right leftState.1 rightState.1 ∧
    leftState.2 = rightState.2

noncomputable def globalHighMonitoredBaseMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp) := fun input =>
  match input with
  | .inl (.inl n) =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalUniformImpl n).run causalState)).run
  | .inl (.inr hashInput) =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey hashInput).run causalState)).run
  | .inr request =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run

noncomputable def globalHighMonitoredMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredTracedState ProbComp) :=
  actionTracedStateImpl (globalHighMonitoredBaseMappedAdversaryImpl right)
    attackerActionFragment

theorem relTriple_globalActionTracedState_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp))
    (rightImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (htrace : leftState.2 = rightState.2)
    (hcouple : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2)) :
    RelTriple
      ((actionTracedStateImpl leftImpl attackerActionFragment input).run
        leftState)
      ((actionTracedStateImpl rightImpl attackerActionFragment input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.2) := by
  let wrapLeft := fun result : (OracleWorld + SigningSpec).Range input ×
      QueryCache HashSpec => (result.1,
    (result.2, leftState.2 ++ attackerActionFragment input result.1))
  let wrapRight := fun result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState => (result.1,
    (result.2, rightState.2 ++ attackerActionFragment input result.1))
  let post := fun leftResult : (OracleWorld + SigningSpec).Range input ×
      SourceTracedState => fun rightResult :
      (OracleWorld + SigningSpec).Range input × GlobalMonitoredTracedState =>
    (leftResult.1 = rightResult.1 ∧
      GlobalMonitoredTracedStateRelation left right leftResult.2
        rightResult.2) ∨ rightResult.2.1.bad right.2
  have hprepared : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · refine Or.inl ⟨hgood.1, hgood.2, ?_⟩
      change leftState.2 ++ attackerActionFragment input leftResult.1 =
        rightState.2 ++ attackerActionFragment input rightResult.1
      rw [htrace, hgood.1]
    · exact Or.inr hbad
  unfold actionTracedStateImpl
  simpa [wrapLeft, wrapRight, post, map_eq_bind_pure_comp] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalHighMonitored_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.1.2) := by
  have liftBase := relTriple_globalActionTracedState_until_bad input left
    right.1 (sourceDirectMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
      (globalHighMonitoredBaseMappedAdversaryImpl right) leftState rightState
        hstate.2
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalHighMonitoredBaseMappedAdversaryImpl, romImpl, unifFwdImpl,
        OracleComp.liftM_run_StateT] using
        (relTriple_programmed_monitoredGlobalUniformQuery left right.1
          leftState.1 rightState.1 hstate.1 n)
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalHighMonitoredBaseMappedAdversaryImpl, romImpl] using
        (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
          right hrel hleftSupport hrightSupport leftState.1 rightState.1
            hstate.1 hashInput)
  · apply liftBase
    simpa [sourceDirectMappedAdversaryImpl,
      unloggedMappedAdversaryImpl_apply_inr,
      globalHighMonitoredBaseMappedAdversaryImpl] using
      (relTriple_programmed_monitoredGlobalSigningQuery left right hrel
        hleftSupport hrightSupport leftState.1 rightState.1 hstate.1 request)

noncomputable def globalHighMonitoredVerifierImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld (StateT GlobalMonitoredTracedState ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      ((globalHighMonitoredBaseMappedAdversaryImpl right (.inl input)).run
        state.1)

theorem relTriple_keepGlobalAttackerTrace_until_bad
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftTrace rightTrace : AttackerActionTrace)
    (htrace : leftTrace = rightTrace)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : ProbComp (α × GlobalMonitoredCausalState))
    (hcouple : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2)) :
    RelTriple
      ((fun result => (result.1, (result.2, leftTrace))) <$> leftComputation)
      ((fun result => (result.1, (result.2, rightTrace))) <$> rightComputation)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.2) := by
  let wrapLeft := fun result : α × QueryCache HashSpec =>
    (result.1, (result.2, leftTrace))
  let wrapRight := fun result : α × GlobalMonitoredCausalState =>
    (result.1, (result.2, rightTrace))
  let post := fun leftResult : α × SourceTracedState =>
    fun rightResult : α × GlobalMonitoredTracedState =>
      (leftResult.1 = rightResult.1 ∧
        GlobalMonitoredTracedStateRelation left right leftResult.2
          rightResult.2) ∨ rightResult.2.1.bad right.2
  have hprepared : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2, htrace⟩
    · exact Or.inr hbad
  simpa [wrapLeft, wrapRight, post] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalHighMonitored_verifier_query
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceDirectTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.1.2) := by
  rw [sourceDirectTracedVerifierImpl_query_run_eq]
  unfold globalHighMonitoredVerifierImpl
  rw [StateT.run_mk]
  apply relTriple_keepGlobalAttackerTrace_until_bad left right.1 leftState.2
    rightState.2 hstate.2
  rcases input with n | hashInput
  · simpa [sourceDirectTracedVerifierImpl,
      globalHighMonitoredVerifierImpl,
      globalHighMonitoredBaseMappedAdversaryImpl, romImpl, unifFwdImpl,
      OracleComp.liftM_run_StateT] using
      (relTriple_programmed_monitoredGlobalUniformQuery left right.1
        leftState.1 rightState.1 hstate.1 n)
  · simpa [sourceDirectTracedVerifierImpl,
      globalHighMonitoredVerifierImpl,
      globalHighMonitoredBaseMappedAdversaryImpl, romImpl] using
      (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
        right hrel hleftSupport hrightSupport leftState.1 rightState.1 hstate.1
          hashInput)

theorem globalMonitoredTracedStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalMonitoredTracedStateRelation left right.1 (left.cache, [])
      (⟨globalFilteredCausalKeygenState right.1.1, []⟩, []) := by
  refine ⟨globalMonitoredFilteredStateRelation_initial left right.1 left.cache
    (globalFilteredCausalKeygenState right.1.1) ?_ ?_ ?_, rfl⟩
  · exact programmedGlobal_filteredKeygen_stateRelation left right hrel
      hleftSupport hrightSupport
  · exact globalFilteredCausalKeygenState_merkleRetained right.1.1
  · intro index
    simp [globalFilteredCausalKeygenState]

noncomputable def sourceGlobalTracedDetailedExecution
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceTracedState) := do
  let handled ← (simulateQ
    (sourceDirectTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run (keyView.cache, [])
  let verified ← (simulateQ sourceDirectTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.leafIndex
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

noncomputable def globalHighMonitoredDetailedExecution
    (adversary : Adversary)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    ProbComp ((Forgery × Bool) × GlobalMonitoredTracedState) := do
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl right)
    (adversary.main right.1.1.publicKey)).run initial
  let verified ← (simulateQ (globalHighMonitoredVerifierImpl right)
    (Concrete.scheme.verify right.1.1.publicKey handled.1.leafIndex
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

def sourceGlobalExecutionResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (execution : (Forgery × Bool) × SourceTracedState) :
    (GameOutcome × QueryCache HashSpec) × AttackerActionTrace :=
  ((actionTraceOutcome keyView.publicKey
    (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
    (execution.1, execution.2.2), execution.2.1), execution.2.2)

abbrev SourceGlobalTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceTracedState)

abbrev GlobalHighMonitoredProgramResult :=
  ((ProgrammedGlobalChainKeygenView ×
    (GlobalChainValueIndex → Digest)) ×
    (GlobalChainEdgeIndex → Digest)) ×
      ((Forgery × Bool) × GlobalMonitoredTracedState)

noncomputable def sourceGlobalTracedProgram
    (adversary : Adversary) :
    ProbComp SourceGlobalTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceGlobalProgramResult
    (result : SourceGlobalTracedProgramResult) :
    GlobalChainActionTracedResult :=
  let execution := sourceGlobalExecutionResult result.1 result.2
  ((result.1, execution.1), execution.2)

noncomputable def globalHighMonitoredProgram
    (adversary : Adversary) :
    ProbComp GlobalHighMonitoredProgramResult := do
  let right ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← globalHighMonitoredDetailedExecution adversary right
  pure (right, execution)

def SourceGlobalHighMonitoredProgramRelation
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      GlobalMonitoredTracedStateRelation left.1 right.1.1 left.2.2
        right.2.2) ∨ right.2.2.1.bad right.1.1.2)


def GlobalCausalRevealsCovered
    (covered : Set GlobalChainValueIndex)
    (state : GlobalCausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → index ∈ covered

def GlobalCausalTraceRevealsCovered
    (covered : Set GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  ∀ index value,
    RevealProbeOracleSimulation.ObservedAction.reveal index value ∈ trace →
      index ∈ covered

def GlobalCausalResultCovered
    (covered : Set GlobalChainValueIndex)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) : Prop :=
  GlobalCausalRevealsCovered covered result.1.2 ∧
    GlobalCausalTraceRevealsCovered covered result.2

def GlobalChainValueIndicesForwardClosed
    (covered : Set GlobalChainValueIndex) : Prop :=
  ∀ chain leafIndex earlier later,
    (chain, leafIndex, earlier) ∈ covered → earlier ≤ later →
      (chain, leafIndex, later) ∈ covered

theorem GlobalCausalTraceRevealsCovered.append
    {covered : Set GlobalChainValueIndex}
    {left right : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex}
    (hleft : GlobalCausalTraceRevealsCovered covered left)
    (hright : GlobalCausalTraceRevealsCovered covered right) :
    GlobalCausalTraceRevealsCovered covered (left ++ right) := by
  intro index value hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft index value hmem
  · exact hright index value hmem

theorem GlobalCausalRevealsCovered.setCache
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (cache : QueryCache HashSpec) :
    GlobalCausalRevealsCovered covered { state with cache := cache } := by
  exact hcovered

theorem GlobalCausalRevealsCovered.recordedState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalRevealsCovered covered
      (globalCausalRecordedState secretKey input state) := by
  intro index value hrevealed
  apply hcovered index value
  simpa only [globalCausalRecordedState_revealed] using hrevealed

theorem GlobalCausalRevealsCovered.recordReveal
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (index : GlobalChainValueIndex) (value : Digest)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered (state.recordReveal index value) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · simpa [heq] using hindex
  · apply hcovered candidate candidateValue
    simpa [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] using hrevealed

theorem GlobalCausalRevealsCovered.revealResultState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered
      (globalFilteredCausalRevealResultState secretKey input state index value
        output) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · subst candidate
    exact hindex
  · apply hcovered candidate candidateValue
    simpa [globalFilteredCausalRevealResultState,
      Function.update_of_ne heq] using hrevealed

noncomputable def GlobalReturnedChainValueCovered
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Set GlobalChainValueIndex :=
  fun index =>
    index.2 ∈ ReturnedChainValueCovered cache secretKey log index.1

theorem globalReturnedChainValueCovered_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) :
    GlobalChainValueIndicesForwardClosed
      (GlobalReturnedChainValueCovered cache secretKey log) := by
  intro chain leafIndex earlier later hmem hle
  exact returnedChainValueCovered_forwardClosed cache secretKey log chain
    leafIndex earlier later hmem hle

theorem globalReturnedChainValueCovered_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (request : SignRequest)
    (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache secretKey.parameter request.leafIndex
        (request.message, signature.randomness)) = some encoding)
    (chain : ChainIndex) :
    (chain, .inl request.leafIndex, encoding chain) ∈
      GlobalReturnedChainValueCovered cache secretKey log := by
  exact returnedChainValueCovered_contains_returned cache secretKey log chain
    request signature encoding hreturned hdecode

theorem globalReturnedChainValueCovered_contains_returnedTop
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (request : SignRequest)
    (signature : Signature) (randomness : Randomness) (topEncoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (htop : secretKey.topSigned (topKeyOf request.leafIndex) = some (randomness, topEncoding))
    (chain : ChainIndex) :
    (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈
      GlobalReturnedChainValueCovered cache secretKey log := by
  exact returnedChainValueCovered_contains_returnedTop cache secretKey log chain
    request signature randomness topEncoding hreturned htop

theorem globalReturnedChainValueCovered_of_comparableCaches
    (parameter : PublicParameter)
    (leftCache rightCache : QueryCache HashSpec)
    (leftSecret rightSecret : SecretKey)
    (leftLog rightLog : QueryLog SigningSpec)
    (hleftParameter : leftSecret.parameter = parameter)
    (hrightParameter : rightSecret.parameter = parameter)
    (hlogs : rightLog = leftLog)
    (htopSigned : leftSecret.topSigned = rightSecret.topSigned)
    (hcaches : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (index : GlobalChainValueIndex)
    (hindex : index ∈
      GlobalReturnedChainValueCovered rightCache rightSecret rightLog) :
    index ∈ GlobalReturnedChainValueCovered leftCache leftSecret
      leftLog := by
  change index.2 ∈ ReturnedChainValueCovered rightCache rightSecret
    rightLog index.1 at hindex
  change index.2 ∈ ReturnedChainValueCovered leftCache leftSecret
    leftLog index.1
  rw [returnedChainValueCovered_iff] at hindex ⊢
  rcases hindex with ⟨request, signature, encoding, hreturned, hdecode, hleafIndex,
    hdigit⟩ | ⟨request, signature, randomness, topEncoding, hreturned, htop, hkey, hdigit⟩
  · have hhash :
        Concrete.CacheView.encodingHash leftCache leftSecret.parameter
            request.leafIndex (request.message, signature.randomness) =
          Concrete.CacheView.encodingHash rightCache rightSecret.parameter
            request.leafIndex (request.message, signature.randomness) := by
      rw [hleftParameter, hrightParameter]
      unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
      rw [hcaches _ ⟨request.leafIndex, request.message, signature.randomness,
        rfl⟩]
    refine Or.inl ⟨request, signature, encoding, ?_, ?_, hleafIndex, hdigit⟩
    · simpa [hlogs] using hreturned
    · rw [hhash]
      exact hdecode
  · refine Or.inr ⟨request, signature, randomness, topEncoding, ?_, ?_, hkey, hdigit⟩
    · simpa [hlogs] using hreturned
    · rw [htopSigned]
      exact htop

theorem globalFilteredCausalLeafHashPlan_ne_reveal
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    globalFilteredCausalLeafHashPlan secretKey input state ≠ .reveal index := by
  unfold globalFilteredCausalLeafHashPlan
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split <;> intro h <;> cases h

theorem globalFilteredCausalUncachedHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest))
    (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalUncachedAttackerHashPlan secretKey input state
      probe = .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  cases probe with
  | none =>
      exact (globalFilteredCausalLeafHashPlan_ne_reveal secretKey input state
        index hplan).elim
  | some probe =>
      obtain ⟨predecessor, target⟩ := probe
      cases hrevealed : state.revealed predecessor with
      | none =>
          simp only [globalFilteredCausalUncachedAttackerHashPlan,
            hrevealed] at hplan
          split at hplan <;> cases hplan
      | some value =>
          by_cases htarget : value = target
          · subst target
            by_cases hnext : predecessor.2.2.val + 1 < chainLength
            · simp only [globalFilteredCausalUncachedAttackerHashPlan,
                hrevealed, dite_eq_left hnext] at hplan
              have hindex :
                  (predecessor.1, predecessor.2.1,
                    ⟨predecessor.2.2.val + 1, hnext⟩) = index :=
                GlobalFilteredCausalHashPlan.reveal.inj hplan
              subst index
              exact ⟨predecessor, value, hrevealed, rfl, rfl, rfl⟩
            · simp only [globalFilteredCausalUncachedAttackerHashPlan,
                hrevealed, dite_eq_right hnext] at hplan
              cases hplan
          · simp only [globalFilteredCausalUncachedAttackerHashPlan,
              hrevealed, ite_eq_right htarget] at hplan
            cases hplan

theorem globalFilteredCausalAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  unfold globalFilteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | some output => simp only [hcache] at hplan; cases hplan
  | none =>
      simp only [hcache] at hplan
      exact globalFilteredCausalUncachedHashPlan_reveal_has_predecessor
        secretKey input state
          (globalChainInputProbe? secretKey.parameter input) index hplan

theorem globalFilteredCausalAttackerHashPlan_reveal_mem_of_covered
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (covered : Set GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered) :
    index ∈ covered := by
  obtain ⟨predecessor, value, hrevealed, hchain, hleafIndex, hnext⟩ :=
    globalFilteredCausalAttackerHashPlan_reveal_has_predecessor secretKey input
      state index hplan
  apply hforward index.1 index.2.1 predecessor.2.2 index.2.2
  · rw [← hchain, ← hleafIndex]
    exact hcovered predecessor value hrevealed
  · change predecessor.2.2.val ≤ index.2.2.val
    omega

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_covered
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    GlobalCausalResultCovered covered result := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | redirect output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | fresh =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | reveal index =>
      have hindex :=
        globalFilteredCausalAttackerHashPlan_reveal_mem_of_covered secretKey
          input state index covered hplan hcovered hforward
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      constructor
      · exact hcovered.revealResultState secretKey input index (table index)
          _ hindex
      · intro candidate value hmem
        simp only [List.mem_singleton,
          RevealProbeOracleSimulation.ObservedAction.reveal.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact hindex
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map]
        at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩



theorem globalSignatureRevealResult_covered
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hindices : ∀ chain ∈ chains,
      (chain, .inl request.leafIndex, encoding chain) ∈ covered) :
    GlobalCausalRevealsCovered covered
        (globalSignatureRevealResult table request encoding chains signature
          state).2 ∧
      GlobalCausalTraceRevealsCovered covered
        (globalSignatureRevealTrace table request encoding chains) := by
  induction chains generalizing signature state with
  | nil =>
      exact ⟨hcovered, by
        simp [globalSignatureRevealTrace,
          GlobalCausalTraceRevealsCovered]⟩
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, .inl request.leafIndex, encoding chain)
      have hindex : index ∈ covered := hindices chain (by simp)
      have htailIndices : ∀ candidate ∈ chains,
          (candidate, .inl request.leafIndex, encoding candidate) ∈ covered := by
        intro candidate hcandidate
        exact hindices candidate (List.mem_cons_of_mem chain hcandidate)
      rw [globalSignatureRevealResult, globalSignatureRevealTrace]
      have htail := ih
        (replaceSignatureChainValue signature chain (table index))
        (state.recordReveal index (table index))
        (hcovered.recordReveal index (table index) hindex) htailIndices
      constructor
      · exact htail.1
      · intro candidate value hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · cases hhead
          exact hindex
        · exact htail.2 candidate value htailMem

theorem globalSignatureTopRevealResult_covered
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hindices : ∀ chain ∈ chains,
      (chain, .inr (topKeyOf request.leafIndex), encoding chain) ∈ covered) :
    GlobalCausalRevealsCovered covered
        (globalSignatureTopRevealResult table request encoding chains signature
          state).2 ∧
      GlobalCausalTraceRevealsCovered covered
        (globalSignatureTopRevealTrace table request encoding chains) := by
  induction chains generalizing signature state with
  | nil =>
      exact ⟨hcovered, by
        simp [globalSignatureTopRevealTrace,
          GlobalCausalTraceRevealsCovered]⟩
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, .inr (topKeyOf request.leafIndex), encoding chain)
      have hindex : index ∈ covered := hindices chain (by simp)
      have htailIndices : ∀ candidate ∈ chains,
          (candidate, .inr (topKeyOf request.leafIndex), encoding candidate) ∈ covered := by
        intro candidate hcandidate
        exact hindices candidate (List.mem_cons_of_mem chain hcandidate)
      rw [globalSignatureTopRevealResult, globalSignatureTopRevealTrace]
      have htail := ih
        (replaceSignatureTopChainValue signature chain (table index))
        (state.recordReveal index (table index))
        (hcovered.recordReveal index (table index) hindex) htailIndices
      constructor
      · exact htail.1
      · intro candidate value hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · cases hhead
          exact hindex
        · exact htail.2 candidate value htailMem

theorem globalSignatureFullRevealResult_covered
    (table : GlobalChainValueIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hindices : ∀ randomness topEncoding,
      topSigned (topKeyOf request.leafIndex) = some (randomness, topEncoding) →
      (∀ chain, (chain, .inl request.leafIndex, encoding chain) ∈ covered) ∧
      ∀ chain, (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered) :
    GlobalCausalRevealsCovered covered
        (globalSignatureFullRevealResult table topSigned request encoding signature
          state).2 ∧
      GlobalCausalTraceRevealsCovered covered
        (globalSignatureFullRevealTrace table topSigned request encoding) := by
  unfold globalSignatureFullRevealResult globalSignatureFullRevealTrace
  cases htop : topSigned (topKeyOf request.leafIndex) with
  | none => exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | some signed =>
      obtain ⟨randomness, topEncoding⟩ := signed
      obtain ⟨hbottom, htopIndices⟩ := hindices randomness topEncoding htop
      have hfirst := globalSignatureRevealResult_covered table request encoding allChains
        signature state covered hcovered (fun chain _ => hbottom chain)
      have hsecond := globalSignatureTopRevealResult_covered table request topEncoding allChains
        (globalSignatureRevealResult table request encoding allChains signature state).1
        (globalSignatureRevealResult table request encoding allChains signature state).2
        covered hfirst.1 (fun chain _ => htopIndices chain)
      exact ⟨hsecond.1, hfirst.2.append hsecond.2⟩

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      Concrete.topSignedAt keyView.secretKey request.leafIndex = true →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.leafIndex
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, .inl request.leafIndex, encoding chain) ∈ covered)
    (htopDirect : ∀ returnedSignature topRandomness topEncoding chain,
      result.1.1 = some returnedSignature →
      keyView.secretKey.topSigned (topKeyOf request.leafIndex) =
        some (topRandomness, topEncoding) →
      (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request randomness state)).run)) :
    GlobalCausalResultCovered covered result := by
  unfold globalFilteredCausalSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨encodedTrace, hencodedTrace, hresult⟩ := hresult
  rw [support_map] at hencodedTrace
  obtain ⟨encoded, hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ⟨hcovered.setCache encoded.2,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignature] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      let initialSignature := Concrete.CacheReplay.signWithEncoding
        keyView.cache keyView.secretKey request.leafIndex randomness encoding
      let encodedState : GlobalCausalHashState := { state with cache := encoded.2 }
      let returned := globalSignatureFullRevealResult table keyView.secretKey.topSigned request
        encoding initialSignature encodedState
      have hstable : Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.leafIndex
          (request.message, randomness) = encoded.1 := by
        apply Concrete.CacheReplay.encodingHash_eq_of_run_support_of_cache_le
          keyView.secretKey.parameter state.cache encoded.2 finalCache
            request.leafIndex request.message randomness encoded.1 hencoded
        simpa [Prod.map, returned, encodedState,
          globalSignatureFullRevealResult_cache]
          using hcacheLe
      have hindices : ∀ topRandomness topEncoding,
          keyView.secretKey.topSigned (topKeyOf request.leafIndex) =
            some (topRandomness, topEncoding) →
          (∀ chain, (chain, .inl request.leafIndex, encoding chain) ∈ covered) ∧
          ∀ chain, (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered := by
        intro topRandomness topEncoding htop
        refine ⟨fun chain => ?_, fun chain => htopDirect returned.1 topRandomness topEncoding
          chain rfl htop⟩
        apply hdirect returned.1 encoding chain
        · rfl
        · simp [Concrete.topSignedAt, htop]
        · simpa [returned, initialSignature,
            Concrete.CacheReplay.signWithEncoding,
            globalSignatureFullRevealResult_randomness, hstable] using hdecode
      simpa [GlobalCausalResultCovered, returned, initialSignature,
        encodedState] using
        (globalSignatureFullRevealResult_covered table keyView.secretKey.topSigned request
          encoding initialSignature encodedState covered (hcovered.setCache encoded.2)
            hindices)

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_covered_of_final
    (attempts trial : Nat) (base : Randomness) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      Concrete.topSignedAt keyView.secretKey request.leafIndex = true →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.leafIndex
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, .inl request.leafIndex, encoding chain) ∈ covered)
    (htopDirect : ∀ returnedSignature topRandomness topEncoding chain,
      result.1.1 = some returnedSignature →
      keyView.secretKey.topSigned (topKeyOf request.leafIndex) =
        some (topRandomness, topEncoding) →
      (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts keyView request base attempts trial
          state)).run)) :
    GlobalCausalResultCovered covered result := by
  induction attempts generalizing trial state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hcontinuation⟩ := hresult
      cases hoption : attemptResult.1.1 with
      | some signature =>
          unfold globalFilteredCausalSignTraceContinuation at hcontinuation
          rw [hoption] at hcontinuation
          simp only [support_pure, Set.mem_singleton_iff] at hcontinuation
          subst result
          exact
            simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
              table keyView request _ state covered finalCache attemptResult
                hcovered hcacheLe hdirect htopDirect hattempt
      | none =>
          unfold globalFilteredCausalSignTraceContinuation at hcontinuation
          rw [hoption, support_map] at hcontinuation
          obtain ⟨rest, hrest, rfl⟩ := hcontinuation
          have hrestCacheLe : rest.1.2.cache ≤ finalCache := hcacheLe
          have hattemptCacheLe : attemptResult.1.2.cache ≤ finalCache :=
            (simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
              attempts (trial + 1) base table keyView request attemptResult.1.2 rest hrest).1.trans
                hrestCacheLe
          have hattemptCovered :=
            simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
              table keyView request _ state covered finalCache attemptResult
                hcovered hattemptCacheLe (by
                  intro returnedSignature encoding chain hreturned _htop _hdecode
                  rw [hoption] at hreturned
                  contradiction) (by
                  intro returnedSignature topRandomness topEncoding chain hreturned _htop
                  rw [hoption] at hreturned
                  contradiction) hattempt
          have hrestCovered := ih (trial + 1) attemptResult.1.2 rest hattemptCovered.1
            hrestCacheLe hdirect htopDirect hrest
          exact ⟨hrestCovered.1,
            hattemptCovered.2.append hrestCovered.2⟩

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_support_covered_of_final
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.leafIndex
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, .inl request.leafIndex, encoding chain) ∈ covered)
    (htopDirect : ∀ returnedSignature topRandomness topEncoding chain,
      result.1.1 = some returnedSignature →
      keyView.secretKey.topSigned (topKeyOf request.leafIndex) =
        some (topRandomness, topEncoding) →
      (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalCausalResultCovered covered result := by
  obtain ⟨base, attemptResult, hattempt, rfl⟩ :=
    mem_support_globalFilteredCausalSigningQuery hresult
  have hcovered' :=
    simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_covered_of_final
      signingAttemptLimit 0 base table keyView request state covered finalCache attemptResult
        hcovered hcacheLe
        (by
          intro returnedSignature encoding chain hreturned htopAt hdecode
          apply hdirect returnedSignature encoding chain _ hdecode
          simp [topSignedResult, htopAt, hreturned])
        (by
          intro returnedSignature topRandomness topEncoding chain hreturned htop
          apply htopDirect returnedSignature topRandomness topEncoding chain _ htop
          simp [topSignedResult, Concrete.topSignedAt, htop, hreturned])
        hattempt
  exact hcovered'

theorem globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (plan : GlobalFilteredCausalHashPlan)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state = plan)
    (hnoncached : ∀ output, plan ≠ .cached output) :
    state.cache input = none := by
  unfold globalFilteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      simp only [hcache] at hplan
      exact (hnoncached output hplan.symm).elim

theorem simulate_eagerTrace_globalCausalHashQuery_support_cache_le
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalHashQuery input).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨sample, hsample, rfl⟩ := hresult
  have hsample' : sample ∈ support
      ((uniformSampleImpl.withCaching input).run state.cache) := by
    simpa [randomOracle] using hsample
  exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
    sample hsample'

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_cache_le
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using
        (le_rfl : state.cache ≤ state.cache)
  | redirect output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      have habsent := globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.redirect output) hplan (by intro; simp)
      simpa [globalFilteredCausalRedirectResultState,
        globalCausalRecordedState_cache] using
          QueryCache.le_cacheQuery state.cache habsent
  | fresh =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simpa only [globalCausalRecordedState_cache] using
        (simulate_eagerTrace_globalCausalHashQuery_support_cache_le table
          input (globalCausalRecordedState secretKey input state) result hresult)
  | reveal index =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      have habsent := globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.reveal index) hplan (by intro; simp)
      simpa [globalFilteredCausalRevealResultState] using
        QueryCache.le_cacheQuery state.cache habsent
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map]
        at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      have hsample' : sample ∈ support
          ((uniformSampleImpl.withCaching input).run state.cache) := by
        simpa [randomOracle] using hsample
      simpa [globalCausalRecordedState_cache,
        GlobalCausalHashState.setCache] using
          (QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
            sample hsample')



def GlobalMonitoredCausalStateCovered
    (covered : Set GlobalChainValueIndex)
    (state : GlobalMonitoredCausalState) : Prop :=
  GlobalCausalRevealsCovered covered state.causal ∧
    GlobalCausalTraceRevealsCovered covered state.trace

theorem simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalUniformImpl n).run state)).run)) :
    result.1.2 = state ∧ result.2 = [] := by
  rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
  obtain ⟨output, _houtput, rfl⟩ := hresult
  exact ⟨rfl, rfl⟩

theorem monitorGlobalCausalTrace_support_covered
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (result : α × GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((monitorGlobalCausalTrace computation).run state))
    (hstep : ∀ raw ∈ support (computation state.causal),
      GlobalCausalResultCovered covered raw) :
    GlobalMonitoredCausalStateCovered covered result.2 := by
  rw [monitorGlobalCausalTrace_run, support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  have hrawCovered := hstep raw hraw
  exact ⟨hrawCovered.1, hcovered.2.append hrawCovered.2⟩

theorem globalHighMonitoredBaseMappedAdversaryImpl_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((globalHighMonitoredBaseMappedAdversaryImpl right input).run state)) :
    state.causal.cache ≤ result.2.causal.cache := by
  rcases input with (n | hashInput) | request
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    have hstate :=
      simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
        right.1.2 n state.causal raw hraw
    simp [globalMonitoredCausalResult, hstate.1]
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    exact
      simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_cache_le
        right.1.2 (globalChainValueHighTableOfEdges right.2)
          right.1.1.secretKey hashInput state.causal raw hraw
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    exact
      (simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
        right.1.2 right.1.1 request state.causal raw hraw).1

set_option maxRecDepth 100000 in
theorem globalHighMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hcacheLe : result.2.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈
        attackerActionFragment input result.1 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          right.1.1.secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding →
      (chain, .inl request.leafIndex, encoding chain) ∈ covered)
    (htopDirect : ∀ request signature topRandomness topEncoding chain,
      AttackerAction.sign request (some signature) ∈ attackerActionFragment input result.1 →
      right.1.1.secretKey.topSigned (topKeyOf request.leafIndex) =
        some (topRandomness, topEncoding) →
      (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered)
    (hresult : result ∈ support
      ((globalHighMonitoredBaseMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2 := by
  rcases input with (n | hashInput) | request
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    apply monitorGlobalCausalTrace_support_covered _ state covered
      hcovered result hresult
    intro raw hraw
    have hstate :=
      simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
        right.1.2 n state.causal raw hraw
    constructor
    · simpa [hstate.1] using hcovered.1
    · simp [hstate.2, GlobalCausalTraceRevealsCovered]
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    apply monitorGlobalCausalTrace_support_covered _ state covered
      hcovered result hresult
    intro raw hraw
    exact
      simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_covered
        right.1.2 (globalChainValueHighTableOfEdges right.2)
          right.1.1.secretKey hashInput state.causal covered hcovered.1 hforward
            raw hraw
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    have hrawCovered :=
      simulate_eagerTrace_globalFilteredCausalSigningQuery_support_covered_of_final
        right.1.2 right.1.1 request state.causal covered finalCache raw
          hcovered.1 (by
            simpa [globalMonitoredCausalResult] using hcacheLe)
          (by
            intro returnedSignature encoding chain hreturned hdecode
            apply hdirect request returnedSignature encoding chain
            · simp [globalMonitoredCausalResult, attackerActionFragment,
                hreturned]
            · exact hdecode)
          (by
            intro returnedSignature topRandomness topEncoding chain hreturned htop
            apply htopDirect request returnedSignature topRandomness topEncoding chain
            · simp [globalMonitoredCausalResult, attackerActionFragment,
                hreturned]
            · exact htop)
          hraw
    exact ⟨hrawCovered.1, hcovered.2.append hrawCovered.2⟩

theorem globalHighMonitoredMappedAdversaryImpl_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact globalHighMonitoredBaseMappedAdversaryImpl_support_cache_le right
    input state.1 baseResult hbaseResult

set_option maxRecDepth 100000 in
theorem globalHighMonitoredMappedAdversaryImpl_support_covered_of_final
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ result.2.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          right.1.1.secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding →
      (chain, .inl request.leafIndex, encoding chain) ∈ covered)
    (htopDirect : ∀ request signature topRandomness topEncoding chain,
      AttackerAction.sign request (some signature) ∈ result.2.2 →
      right.1.1.secretKey.topSigned (topKeyOf request.leafIndex) =
        some (topRandomness, topEncoding) →
      (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  apply globalHighMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    right input state.1 covered finalCache hcovered hforward baseResult hcacheLe
  · intro request signature encoding chain haction hdecode
    apply hdirect request signature encoding chain
    · exact List.mem_append_right state.2 haction
    · exact hdecode
  · intro request signature topRandomness topEncoding chain haction htop
    exact htopDirect request signature topRandomness topEncoding chain
      (List.mem_append_right state.2 haction) htop
  · exact hbaseResult

theorem globalHighMonitoredMappedAdversaryImpl_preserves_cache_extension
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialCache : QueryCache HashSpec) :
    QueryImpl.PreservesInv (globalHighMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        initialCache ≤ state.1.causal.cache) := by
  intro input state hstate result hresult
  exact hstate.trans
    (globalHighMonitoredMappedAdversaryImpl_support_cache_le right input state
      result hresult)

theorem globalHighMonitoredMappedAdversaryImpl_preserves_trace_extension
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialTrace : AttackerActionTrace) :
    QueryImpl.PreservesInv (globalHighMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        ∀ action ∈ initialTrace, action ∈ state.2) := by
  intro input state hstate result hresult
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
  intro action haction
  exact List.mem_append_left _ (hstate action haction)

theorem simulate_globalHighMonitoredMappedAdversary_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    (fun current : GlobalMonitoredTracedState =>
      state.1.causal.cache ≤ current.1.causal.cache)
    (globalHighMonitoredMappedAdversaryImpl_preserves_cache_extension right
      state.1.causal.cache) computation state le_rfl result hresult

theorem simulate_globalHighMonitoredMappedAdversary_support_trace_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    ∀ action ∈ state.2, action ∈ result.2.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    (fun current : GlobalMonitoredTracedState =>
      ∀ action ∈ state.2, action ∈ current.2)
    (globalHighMonitoredMappedAdversaryImpl_preserves_trace_extension right
      state.2) computation state (by simp) result hresult

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem simulate_globalHighMonitoredMappedAdversary_support_covered_of_final
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (finalTrace : AttackerActionTrace)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          right.1.1.secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding →
      (chain, .inl request.leafIndex, encoding chain) ∈ covered)
    (htopDirect : ∀ request signature topRandomness topEncoding chain,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      right.1.1.secretKey.topSigned (topKeyOf request.leafIndex) =
        some (topRandomness, topEncoding) →
      (chain, .inr (topKeyOf request.leafIndex), topEncoding chain) ∈ covered)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state))
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.2.2 → action ∈ finalTrace) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hheadCacheLe : head.2.1.causal.cache ≤ finalCache :=
        (simulate_globalHighMonitoredMappedAdversary_support_cache_le right
          (next head.1) head.2 result htail).trans hcacheLe
      have hheadTraceLe : ∀ action, action ∈ head.2.2 →
          action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact simulate_globalHighMonitoredMappedAdversary_support_trace_le right
          (next head.1) head.2 result htail action haction
      have hheadCovered :=
        globalHighMonitoredMappedAdversaryImpl_support_covered_of_final right
          input state covered finalCache hcovered hforward head hheadCacheLe
            (fun request signature encoding chain haction hdecode =>
              hdirect request signature encoding chain
                (hheadTraceLe _ haction) hdecode)
            (fun request signature topRandomness topEncoding chain haction htop =>
              htopDirect request signature topRandomness topEncoding chain
                (hheadTraceLe _ haction) htop)
            hhead
      exact ih head.1 head.2 hheadCovered result htail hcacheLe htraceLe

theorem globalHighMonitoredVerifierImpl_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain) (state : GlobalMonitoredTracedState)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact globalHighMonitoredBaseMappedAdversaryImpl_support_cache_le right
    (.inl input) state.1 baseResult hbaseResult

theorem globalHighMonitoredVerifierImpl_support_covered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain) (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  apply globalHighMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    right (.inl input) state.1 covered baseResult.2.causal.cache hcovered
      hforward baseResult le_rfl
  · intro request signature encoding chain haction _hdecode
    rcases input with n | hashInput
    · simp [attackerActionFragment] at haction
    · simp [attackerActionFragment] at haction
  · intro request signature topRandomness topEncoding chain haction _htop
    rcases input with n | hashInput
    · simp [attackerActionFragment] at haction
    · simp [attackerActionFragment] at haction
  · exact hbaseResult

theorem globalHighMonitoredVerifierImpl_preserves_cache_extension
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialCache : QueryCache HashSpec) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState =>
        initialCache ≤ state.1.causal.cache) := by
  intro input state hstate result hresult
  exact hstate.trans
    (globalHighMonitoredVerifierImpl_support_cache_le right input state result
      hresult)

theorem globalHighMonitoredVerifierImpl_preserves_covered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (covered : Set GlobalChainValueIndex)
    (hforward : GlobalChainValueIndicesForwardClosed covered) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState =>
        GlobalMonitoredCausalStateCovered covered state.1) := by
  intro input state hstate result hresult
  exact globalHighMonitoredVerifierImpl_support_covered right input state
    covered hstate hforward result hresult

theorem globalHighMonitoredVerifierImpl_preserves_attacker_trace
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialTrace : AttackerActionTrace) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState => state.2 = initialTrace) := by
  intro input state hstate result hresult
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, _hbaseResult, rfl⟩ := hresult
  exact hstate

theorem simulate_globalHighMonitoredVerifier_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun current : GlobalMonitoredTracedState =>
      state.1.causal.cache ≤ current.1.causal.cache)
    (globalHighMonitoredVerifierImpl_preserves_cache_extension right
      state.1.causal.cache) computation state le_rfl result hresult

theorem simulate_globalHighMonitoredVerifier_support_covered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun current : GlobalMonitoredTracedState =>
      GlobalMonitoredCausalStateCovered covered current.1)
    (globalHighMonitoredVerifierImpl_preserves_covered right covered hforward)
      computation state hcovered result hresult

theorem simulate_globalHighMonitoredVerifier_support_attacker_trace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        state)) :
    result.2.2 = state.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun current : GlobalMonitoredTracedState => current.2 = state.2)
    (globalHighMonitoredVerifierImpl_preserves_attacker_trace right state.2)
      computation state rfl result hresult

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000000 in
theorem globalHighMonitoredDetailedExecution_support_returnedCovered
    (adversary : Adversary)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (result : (Forgery × Bool) × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      (globalHighMonitoredDetailedExecution adversary right)) :
    GlobalMonitoredCausalStateCovered
      (GlobalReturnedChainValueCovered result.2.1.causal.cache
        right.1.1.secretKey result.2.2.toSigningLog) result.2.1 := by
  unfold globalHighMonitoredDetailedExecution at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨verified, hvertified, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  let covered := GlobalReturnedChainValueCovered
    verified.2.1.causal.cache right.1.1.secretKey
      verified.2.2.toSigningLog
  have hforward : GlobalChainValueIndicesForwardClosed covered :=
    globalReturnedChainValueCovered_forwardClosed verified.2.1.causal.cache
      right.1.1.secretKey verified.2.2.toSigningLog
  have hinitial : GlobalMonitoredCausalStateCovered covered
      ⟨globalFilteredCausalKeygenState right.1.1, []⟩ := by
    constructor
    · intro index value hrevealed
      simp [globalFilteredCausalKeygenState] at hrevealed
    · simp [GlobalCausalTraceRevealsCovered]
  have hhandledCacheLe : handled.2.1.causal.cache ≤
      verified.2.1.causal.cache :=
    simulate_globalHighMonitoredVerifier_support_cache_le right
      (Concrete.scheme.verify right.1.1.publicKey handled.1.leafIndex
        handled.1.message handled.1.signature) handled.2 verified hvertified
  have hhandledCovered : GlobalMonitoredCausalStateCovered covered
      handled.2.1 := by
    apply simulate_globalHighMonitoredMappedAdversary_support_covered_of_final
      right (adversary.main right.1.1.publicKey)
        (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
        covered verified.2.1.causal.cache verified.2.2 hinitial hforward
    · intro request signature encoding chain haction hdecode
      exact globalReturnedChainValueCovered_contains_returned
        verified.2.1.causal.cache right.1.1.secretKey
          verified.2.2.toSigningLog request signature encoding
            (verified.2.2.sign_mem_toSigningLog request signature haction)
              hdecode chain
    · intro request signature topRandomness topEncoding chain haction htop
      exact globalReturnedChainValueCovered_contains_returnedTop
        verified.2.1.causal.cache right.1.1.secretKey
          verified.2.2.toSigningLog request signature topRandomness topEncoding
            (verified.2.2.sign_mem_toSigningLog request signature haction)
              htop chain
    · exact hhandled
    · exact hhandledCacheLe
    · intro action haction
      rw [simulate_globalHighMonitoredVerifier_support_attacker_trace_eq right
        (Concrete.scheme.verify right.1.1.publicKey handled.1.leafIndex
          handled.1.message handled.1.signature) handled.2 verified hvertified]
      exact haction
  exact simulate_globalHighMonitoredVerifier_support_covered right
    (Concrete.scheme.verify right.1.1.publicKey handled.1.leafIndex
      handled.1.message handled.1.signature) handled.2 covered hhandledCovered
        hforward verified hvertified


theorem globalRunObserved_eq_true_of_probe_mem_of_no_reveal
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : state.revealed index = none)
    (hprobe : RevealProbeOracleSimulation.ObservedAction.probe index target ∈
      trace)
    (hhit : table index = target)
    (hnoreveal : ∀ value,
      RevealProbeOracleSimulation.ObservedAction.reveal index value ∉ trace) :
    RevealProbeOracleSimulation.runObserved table state trace = true := by
  induction trace generalizing state with
  | nil => simp at hprobe
  | cons action trace ih =>
      cases action with
      | probe candidate candidateTarget =>
          rw [List.mem_cons] at hprobe
          rcases hprobe with heq | htail
          · cases heq
            rw [RevealProbeOracleSimulation.runObserved, hhidden]
            apply RevealProbeOracleSimulation.runObserved_eq_true_of_initial_tableHit
            unfold RevealProbeOracleSimulation.tableHits
            simp only [decide_eq_true_eq]
            refine ⟨index, ?_⟩
            simp [AdaptiveRevealMonitor.State.addPending, hhit]
          · simp only [RevealProbeOracleSimulation.runObserved]
            cases hrevealed : state.revealed candidate with
            | some value =>
                apply ih state hhidden htail
                intro revealValue hmem
                exact hnoreveal revealValue (by simp [hmem])
            | none =>
                apply ih (state.addPending candidate candidateTarget)
                · exact hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])
      | reveal candidate value =>
          have hne : candidate ≠ index := by
            intro heq
            subst candidate
            exact hnoreveal value (by simp)
          have htail :
              RevealProbeOracleSimulation.ObservedAction.probe index target ∈
                trace := by
            simpa using hprobe
          simp only [RevealProbeOracleSimulation.runObserved]
          cases hrevealed : state.revealed candidate with
          | some previous =>
              apply ih state hhidden htail
              intro revealValue hmem
              exact hnoreveal revealValue (by simp [hmem])
          | none =>
              by_cases hearly : table candidate ∈ state.pending candidate
              · simp [hearly]
              · rw [ite_eq_right hearly]
                apply ih (state.install candidate (table candidate))
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne (Ne.symm hne)] using hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])

def globalHighMonitoredErasedResult
    (result : GlobalHighMonitoredProgramResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  let keyView := result.1.1.1
  let execution := result.2
  ((((keyView.publicKey, keyView.secretKey), keyView.cache),
    (actionTraceOutcome keyView.publicKey keyView.secretKey
      (execution.1, execution.2.2), execution.2.1.causal.cache)),
    execution.2.2)

/-- A probe of the forgery's top value at every digit of every top chain of its top key. -/
def globalForgeryTopProbeTrace (forgery : Forgery) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (List.ofFn fun chain : ChainIndex => List.ofFn fun digit : Digit =>
    RevealProbeOracleSimulation.ObservedAction.probe
      (chain, .inr (topKeyOf forgery.leafIndex), digit)
      (forgery.signature.top.chainValue chain)).flatten

/-- The number of probes the forgery's primary trace makes. -/
def forgeryProbeCount : Nat := numChains + numChains * chainLength

noncomputable def globalForgeryPrimaryProbeTrace
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  let encoding := actionTracedForgeryEncoding result
  (List.ofFn fun chain : ChainIndex =>
    RevealProbeOracleSimulation.ObservedAction.probe
      (chain, .inl result.1.2.1.forgery.leafIndex, encoding chain)
      (result.1.2.1.forgery.signature.chainValue chain)) ++
    globalForgeryTopProbeTrace result.1.2.1.forgery

theorem globalForgeryPrimaryProbeTrace_all_probes
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (action : RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex)
    (haction : action ∈ globalForgeryPrimaryProbeTrace result) :
    ∃ index target, action = .probe index target := by
  unfold globalForgeryPrimaryProbeTrace globalForgeryTopProbeTrace at haction
  simp only [List.mem_append, List.mem_ofFn, List.mem_flatten] at haction
  rcases haction with ⟨chain, rfl⟩ | ⟨_, ⟨chain, rfl⟩, haction⟩
  · exact ⟨_, _, rfl⟩
  · simp only [List.mem_ofFn] at haction
    obtain ⟨digit, rfl⟩ := haction
    exact ⟨_, _, rfl⟩

theorem globalForgeryPrimaryProbeTrace_length
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    (globalForgeryPrimaryProbeTrace result).length = forgeryProbeCount := by
  unfold globalForgeryPrimaryProbeTrace globalForgeryTopProbeTrace forgeryProbeCount
  simp only [List.length_append, List.length_ofFn, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

theorem globalForgeryTopProbeTrace_mem
    (forgery : Forgery) (chain : ChainIndex) (digit : Digit) :
    RevealProbeOracleSimulation.ObservedAction.probe
        (chain, .inr (topKeyOf forgery.leafIndex), digit)
        (forgery.signature.top.chainValue chain) ∈
      globalForgeryTopProbeTrace forgery := by
  unfold globalForgeryTopProbeTrace
  exact List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨chain, rfl⟩, List.mem_ofFn.2 ⟨digit, rfl⟩⟩

noncomputable def globalHighMonitoredPublicProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (Unit × RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) :=
  (result.1.1.2,
    ((), result.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
      (globalHighMonitoredErasedResult result)))

theorem globalForgeryPrimaryProbeTrace_mem
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (chain : ChainIndex) :
    RevealProbeOracleSimulation.ObservedAction.probe
        (chain, .inl result.1.2.1.forgery.leafIndex,
          actionTracedForgeryEncoding result chain)
        (result.1.2.1.forgery.signature.chainValue chain) ∈
      globalForgeryPrimaryProbeTrace result := by
  unfold globalForgeryPrimaryProbeTrace
  exact List.mem_append_left _ (by simp)

theorem sourceGlobalTracedProgram_support_keyView
    (adversary : Adversary)
    (result : SourceGlobalTracedProgramResult)
    (hresult : result ∈ support (sourceGlobalTracedProgram adversary)) :
    result.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  unfold sourceGlobalTracedProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, _hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem globalHighMonitoredProgram_support_info
    (adversary : Adversary)
    (result : GlobalHighMonitoredProgramResult)
    (hresult : result ∈ support (globalHighMonitoredProgram adversary)) :
    result.1.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen ∧
      result.2 ∈ support
        (globalHighMonitoredDetailedExecution adversary result.1) := by
  unfold globalHighMonitoredProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨right, hright, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact ⟨coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
    hright, hexecution⟩

set_option maxRecDepth 1000000 in
theorem sourceGlobal_origin_implies_right_publicObservedHit
    (adversary : Adversary)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hrel : SourceGlobalHighMonitoredProgramRelation left right)
    (horigin : GlobalWinningOutcomeChainValueHasKeygenOrigin
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1) :
    RevealProbeOracleSimulation.ObservedHit
      (globalHighMonitoredPublicProjection right) := by
  rcases hrel.2 with hgood | hbad
  · obtain ⟨chain, hchainOrigin⟩ := horigin
    obtain ⟨encoding, hdecode, hvalue⟩ :=
      winningOutcomeChainValueHasKeygenOrigin_eq_table
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
        (eraseGlobalChainKeygenView
          (sourceGlobalProgramResult left)).1.1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1
        chain hchainOrigin
    have hleftKeySupport :=
      sourceGlobalTracedProgram_support_keyView adversary left hleftSupport
    obtain ⟨hrightKeySupport, hrightExecutionSupport⟩ :=
      globalHighMonitoredProgram_support_info adversary right hrightSupport
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal,
      _hretained⟩ := hgood.2.1
    have hparameter : left.1.secretKey.parameter =
        right.1.1.1.secretKey.parameter :=
      (programmedGlobal_secretKey_parameter_eq left.1 right.1 hrel.1
        hleftKeySupport hrightKeySupport).symm
    have hforgery : left.2.1.1 = right.2.1.1 :=
      congrArg Prod.fst hgood.1
    have htrace : left.2.2.2 = right.2.2.2 := hgood.2.2
    have hdecodeLeft : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash left.2.2.1
          left.1.secretKey.parameter left.2.1.1.leafIndex
          (left.2.1.1.message, left.2.1.1.signature.randomness)) =
        some encoding := by
      simpa [sourceGlobalProgramResult, sourceGlobalExecutionResult,
        eraseGlobalChainKeygenView, actionTraceOutcome,
        Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey] using hdecode
    have hsourceUnrevealed :
        (chain, .inl left.2.1.1.leafIndex, encoding chain) ∉
          GlobalReturnedChainValueCovered left.2.2.1 left.1.secretKey
            left.2.2.2.toSigningLog := by
      change (_, _) ∉ ReturnedChainValueCovered _ _ _ chain
      rw [returnedChainValueCovered_iff_mem_indices]
      exact hchainOrigin.1.forged_chain_coordinate_not_mem_returned encoding
        hdecodeLeft
    have hhash : Concrete.CacheView.encodingHash left.2.2.1
          left.1.secretKey.parameter left.2.1.1.leafIndex
          (left.2.1.1.message, left.2.1.1.signature.randomness) =
        Concrete.CacheView.encodingHash right.2.2.1.causal.cache
          left.1.secretKey.parameter left.2.1.1.leafIndex
          (left.2.1.1.message, left.2.1.1.signature.randomness) := by
      unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
      rw [hcausal.1 _ ⟨left.2.1.1.leafIndex, left.2.1.1.message,
        left.2.1.1.signature.randomness, rfl⟩]
    have hrightDecode : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash right.2.2.1.causal.cache
          right.1.1.1.secretKey.parameter right.2.1.1.leafIndex
          (right.2.1.1.message, right.2.1.1.signature.randomness)) =
        some encoding := by
      rw [← hparameter, ← hforgery, ← hhash]
      exact hdecodeLeft
    have hencoding : actionTracedForgeryEncoding
        (globalHighMonitoredErasedResult right) = encoding := by
      unfold actionTracedForgeryEncoding
      rw [show Concrete.CacheView.encodingHash
          (globalHighMonitoredErasedResult right).1.2.2
          (globalHighMonitoredErasedResult right).1.1.1.2.parameter
          (globalHighMonitoredErasedResult right).1.2.1.forgery.leafIndex
          ((globalHighMonitoredErasedResult right).1.2.1.forgery.message,
            (globalHighMonitoredErasedResult
              right).1.2.1.forgery.signature.randomness) =
          Concrete.CacheView.encodingHash right.2.2.1.causal.cache
            right.1.1.1.secretKey.parameter right.2.1.1.leafIndex
            (right.2.1.1.message, right.2.1.1.signature.randomness) by
        rfl]
      rw [hrightDecode]
      rfl
    have hleftTable := trajectoryProgrammedGlobalChainKeygen_support_table
      left.1 hleftKeySupport
    have htables : left.1.table = right.1.1.2 :=
      hrel.1.1.toStable.1.1
    have hvalueLeft : left.2.1.1.signature.chainValue chain =
        globalKeygenChainValueTable left.1.cache left.1.secretKey
          (chain, .inl left.2.1.1.leafIndex, encoding chain) := by
      simpa [sourceGlobalProgramResult, sourceGlobalExecutionResult,
        eraseGlobalChainKeygenView, actionTraceOutcome,
        globalKeygenChainValueTable, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, keygenChainValueTable] using hvalue
    have hrightValue : right.1.1.2
        (chain, .inl right.2.1.1.leafIndex, encoding chain) =
          right.2.1.1.signature.chainValue chain := by
      rw [hforgery, hleftTable, htables] at hvalueLeft
      exact hvalueLeft.symm
    have hrightUnrevealed :
        (chain, .inl right.2.1.1.leafIndex, encoding chain) ∉
          GlobalReturnedChainValueCovered right.2.2.1.causal.cache
            right.1.1.1.secretKey right.2.2.2.toSigningLog := by
      intro hmem
      apply hsourceUnrevealed
      apply globalReturnedChainValueCovered_of_comparableCaches
        left.1.secretKey.parameter left.2.2.1 right.2.2.1.causal.cache
          left.1.secretKey right.1.1.1.secretKey left.2.2.2.toSigningLog
            right.2.2.2.toSigningLog
      · rfl
      · exact hparameter.symm
      · exact congrArg AttackerActionTrace.toSigningLog htrace.symm
      · exact hrel.1.1.toStable.1.2.2.1
      · exact hcausal.1
      · simpa [hforgery] using hmem
    have hcovered :=
      globalHighMonitoredDetailedExecution_support_returnedCovered adversary
        right.1 right.2 hrightExecutionSupport
    let index : GlobalChainValueIndex :=
      (chain, .inl right.2.1.1.leafIndex, encoding chain)
    let target := right.2.1.1.signature.chainValue chain
    have hprobe : RevealProbeOracleSimulation.ObservedAction.probe index target ∈
        right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right) := by
      apply List.mem_append_right
      change RevealProbeOracleSimulation.ObservedAction.probe
          (chain, .inl right.2.1.1.leafIndex, encoding chain)
          (right.2.1.1.signature.chainValue chain) ∈
        globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right)
      have hprimary := globalForgeryPrimaryProbeTrace_mem
        (globalHighMonitoredErasedResult right) chain
      rw [congrFun hencoding chain] at hprimary
      simpa [globalHighMonitoredErasedResult, actionTraceOutcome] using hprimary
    have hnoreveal : ∀ value,
        RevealProbeOracleSimulation.ObservedAction.reveal index value ∉
          right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
            (globalHighMonitoredErasedResult right) := by
      intro value hmem
      rcases List.mem_append.mp hmem with hprefix | hsuffix
      · exact hrightUnrevealed
          (hcovered.2 index value (by simpa [index] using hprefix))
      · obtain ⟨_, _, hprobe⟩ := globalForgeryPrimaryProbeTrace_all_probes _ _ hsuffix
        cases hprobe
    unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection]
    apply globalRunObserved_eq_true_of_probe_mem_of_no_reveal
      right.1.1.2 AdaptiveRevealMonitor.State.empty
        (right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right)) index target
    · simp [AdaptiveRevealMonitor.State.empty]
    · exact hprobe
    · simpa [index, target] using hrightValue
    · exact hnoreveal
  · unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection]
    apply RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
    exact right.2.2.1.bad_implies_runObserved right.1.1.2 hbad

/-- A forged top chain value that is the hidden honest value at a coordinate no returned signature
revealed. -/
noncomputable def GlobalWinningOutcomeTopChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) : Prop :=
  ∃ chain digit,
    outcome.forgery.signature.top.chainValue chain =
      globalKeygenChainValueTable keygenCache secretKey
        (chain, .inr (topKeyOf outcome.forgery.leafIndex), digit) ∧
    (.inr (topKeyOf outcome.forgery.leafIndex), digit) ∉
      returnedChainValueIndices finalCache secretKey outcome.signingLog chain

set_option maxRecDepth 1000000 in
theorem sourceGlobal_topOrigin_implies_right_publicObservedHit
    (adversary : Adversary)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hrel : SourceGlobalHighMonitoredProgramRelation left right)
    (horigin : GlobalWinningOutcomeTopChainValueHasKeygenOrigin
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1) :
    RevealProbeOracleSimulation.ObservedHit
      (globalHighMonitoredPublicProjection right) := by
  rcases hrel.2 with hgood | hbad
  · obtain ⟨chain, digit, hvalue, hnotReturned⟩ := horigin
    have hleftKeySupport :=
      sourceGlobalTracedProgram_support_keyView adversary left hleftSupport
    obtain ⟨hrightKeySupport, hrightExecutionSupport⟩ :=
      globalHighMonitoredProgram_support_info adversary right hrightSupport
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal,
      _hretained⟩ := hgood.2.1
    have hparameter : left.1.secretKey.parameter =
        right.1.1.1.secretKey.parameter :=
      (programmedGlobal_secretKey_parameter_eq left.1 right.1 hrel.1
        hleftKeySupport hrightKeySupport).symm
    have hforgery : left.2.1.1 = right.2.1.1 :=
      congrArg Prod.fst hgood.1
    have htrace : left.2.2.2 = right.2.2.2 := hgood.2.2
    have hsourceUnrevealed :
        (chain, .inr (topKeyOf left.2.1.1.leafIndex), digit) ∉
          GlobalReturnedChainValueCovered left.2.2.1 left.1.secretKey
            left.2.2.2.toSigningLog := by
      change (_, _) ∉ ReturnedChainValueCovered _ _ _ chain
      rw [returnedChainValueCovered_iff_mem_indices]
      exact hnotReturned
    have hleftTable := trajectoryProgrammedGlobalChainKeygen_support_table
      left.1 hleftKeySupport
    have htables : left.1.table = right.1.1.2 :=
      hrel.1.1.toStable.1.1
    have hvalueLeft : left.2.1.1.signature.top.chainValue chain =
        globalKeygenChainValueTable left.1.cache left.1.secretKey
          (chain, .inr (topKeyOf left.2.1.1.leafIndex), digit) := by
      simpa [sourceGlobalProgramResult, sourceGlobalExecutionResult,
        eraseGlobalChainKeygenView, actionTraceOutcome,
        Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, globalKeygenChainValueTable,
        keygenChainValueTable] using hvalue
    have hrightValue : right.1.1.2
        (chain, .inr (topKeyOf right.2.1.1.leafIndex), digit) =
          right.2.1.1.signature.top.chainValue chain := by
      rw [hforgery, hleftTable, htables] at hvalueLeft
      exact hvalueLeft.symm
    have hrightUnrevealed :
        (chain, .inr (topKeyOf right.2.1.1.leafIndex), digit) ∉
          GlobalReturnedChainValueCovered right.2.2.1.causal.cache
            right.1.1.1.secretKey right.2.2.2.toSigningLog := by
      intro hmem
      apply hsourceUnrevealed
      apply globalReturnedChainValueCovered_of_comparableCaches
        left.1.secretKey.parameter left.2.2.1 right.2.2.1.causal.cache
          left.1.secretKey right.1.1.1.secretKey left.2.2.2.toSigningLog
            right.2.2.2.toSigningLog
      · rfl
      · exact hparameter.symm
      · exact congrArg AttackerActionTrace.toSigningLog htrace.symm
      · exact hrel.1.1.toStable.1.2.2.1
      · exact hcausal.1
      · simpa [hforgery] using hmem
    have hcovered :=
      globalHighMonitoredDetailedExecution_support_returnedCovered adversary
        right.1 right.2 hrightExecutionSupport
    let index : GlobalChainValueIndex :=
      (chain, .inr (topKeyOf right.2.1.1.leafIndex), digit)
    let target := right.2.1.1.signature.top.chainValue chain
    have hprobe : RevealProbeOracleSimulation.ObservedAction.probe index target ∈
        right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right) := by
      apply List.mem_append_right
      unfold globalForgeryPrimaryProbeTrace
      apply List.mem_append_right
      exact globalForgeryTopProbeTrace_mem right.2.1.1 chain digit
    have hnoreveal : ∀ value,
        RevealProbeOracleSimulation.ObservedAction.reveal index value ∉
          right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
            (globalHighMonitoredErasedResult right) := by
      intro value hmem
      rcases List.mem_append.mp hmem with hprefix | hsuffix
      · exact hrightUnrevealed
          (hcovered.2 index value (by simpa [index] using hprefix))
      · obtain ⟨_, _, hprobe⟩ := globalForgeryPrimaryProbeTrace_all_probes _ _ hsuffix
        cases hprobe
    unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection]
    apply globalRunObserved_eq_true_of_probe_mem_of_no_reveal
      right.1.1.2 AdaptiveRevealMonitor.State.empty
        (right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right)) index target
    · simp [AdaptiveRevealMonitor.State.empty]
    · exact hprobe
    · simpa [index, target] using hrightValue
    · exact hnoreveal
  · unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection]
    apply RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
    exact right.2.2.1.bad_implies_runObserved right.1.1.2 hbad

end XmssSecurity.CappedChain
