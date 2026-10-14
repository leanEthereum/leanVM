import Whir.WHIRPhysicalDriver
import Whir.WHIRSourceFrozenPrefix
import Whir.WHIRSourceCatalog
import Whir.WHIRNativeEvent

namespace Whir.WHIRPhysicalBinding
open Concrete Protocol FiatShamirGame DuplexModeGame MerkleTransport
open RawOracleCoupling RawOracleCoupling.Concrete
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRPhysicalSoundness
open PublicMerkleProgram (Runs)
set_option maxHeartbeats 800000

/-- Every sampler reply retained by the actual reader is the answer to that
same canonical physical coordinate, even though PoW and Merkle calls intervene. -/
theorem readPhysicalPackets_real_history {cap : Nat} {R : Type} (C : PrimitiveOracle)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (lanes : Nat) (proofs : Array PrunedMerklePaths)
    (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) (state : WireState p)
    (next : WireState p → List (Sigma (GroupAnswer ctx Q)) → WHIRSourceChronology.Source cap (Option R))
    (observations : List Observation) (result : R)
    (answers : ∀ observation ∈ observations, observation.answer = realAnswer C ctx.iv observation.query)
    (run : Runs (WHIRSourceChronology.erase
      (readPhysicalPackets ctx stack Q p lanes proofs none packets profiles state next)) observations (some result)) :
    ∃ final suffix, Runs (WHIRSourceChronology.erase
      (next final (WHIRModeFinal.realHistory ctx Q C packets))) suffix (some result) := by
  induction packets generalizing state next observations with
  | nil => exact ⟨state,observations,run⟩
  | cons packet packets ih =>
    simp only [readPhysicalPackets] at run
    cases parsed : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) with
    | none => simp only [parsed,WHIRSourceChronology.erase] at run; cases run
    | some value =>
      obtain ⟨absorbed,root⟩ := value
      simp only [parsed] at run
      split at run
      · rw [announce_erase,sourceLift_erase] at run
        obtain ⟨before,nonce,after,trace,_,continued⟩ := (Runs.bind_iff _ _).mp run
        have afterAnswers : ∀ observation ∈ after,
            observation.answer = realAnswer C ctx.iv observation.query := by
          intro observation member
          apply answers observation
          rw [trace]
          exact List.mem_append_right before member
        cases boundNonce : afterNonce absorbed nonce with
        | none => simp only [boundNonce,WHIRSourceChronology.erase] at continued; cases continued
        | some bound =>
          simp only [boundNonce] at continued
          split at continued
          · rw [sourceLift_erase] at continued
            obtain ⟨beforeRaw,raw,afterRaw,traceRaw,sampled,read⟩ := (Runs.bind_iff _ _).mp continued
            have rawAnswers : ∀ observation ∈ beforeRaw,
                observation.answer = realAnswer C ctx.iv observation.query := by
              intro observation member
              apply afterAnswers observation
              rw [traceRaw]
              exact List.mem_append_left afterRaw member
            have actual := (PublicMerkleProgram.Runs.real_result_trace sampled C ctx.iv rawAnswers).1
            rw [readPacket_eq,WHIRModeProgram.readPacket_result] at actual
            have sampleEq : raw = WHIRModeFinal.realPacket ctx Q C packet := actual.symm
            rw [sourceLift_erase] at read
            obtain ⟨beforeOpen,opened,afterOpen,traceOpen,_,rest⟩ := (Runs.bind_iff _ _).mp read
            cases opened with
            | none => cases rest
            | some checked =>
              have restAnswers : ∀ observation ∈ afterOpen,
                  observation.answer = realAnswer C ctx.iv observation.query := by
                intro observation member
                apply afterAnswers observation
                rw [traceRaw,traceOpen]
                exact List.mem_append_right beforeRaw (List.mem_append_right beforeOpen member)
              obtain ⟨final,suffix,last⟩ := ih _ _ _ _ restAnswers rest
              refine ⟨final,suffix,?_⟩
              simpa only [WHIRModeFinal.realHistory,List.map_cons,sampleEq] using last
          · cases continued
      · cases run

private theorem done_result {R : Type} (left right : R) (trace : List Observation)
    (run : Runs (.done left) trace right) : left = right := by
  cases run
  rfl

theorem verifySource_real_history (C : PrimitiveOracle) (cap : Nat)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q lanes : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (proofs : Array PrunedMerklePaths) (observations : List Observation) (v : Verified ctx Q cap packet)
    (answers : ∀ observation ∈ observations, observation.answer = realAnswer C ctx.iv observation.query)
    (run : Runs (WHIRSourceChronology.erase (verifySource cap model ctx stack Q lanes packet proofs))
      observations (some v)) :
    v.history = WHIRModeFinal.realHistory ctx Q C (completion ctx Q packet) := by
  obtain ⟨root,before,after,request,_,_,trace,_,_,decoded,physical⟩ :=
    WHIRPhysicalCaller.verifySource_success cap model ctx stack Q lanes packet proofs observations v run
  have afterAnswers : ∀ observation ∈ after,
      observation.answer = realAnswer C ctx.iv observation.query := by
    intro observation member
    apply answers observation
    rw [trace]
    exact List.mem_append_right before member
  obtain ⟨wire,suffix,last⟩ := readPhysicalPackets_real_history C ctx stack Q packet.val.profile
    request.lanes proofs (completion ctx Q packet) (completion_profiles ctx Q packet)
    (initialWireState packet.val.profile root) _ after v afterAnswers physical
  exact (WHIRPhysicalCaller.finish_success ctx Q cap packet request wire _ _ _ v
    (done_result _ _ suffix last)).2.2

theorem local_realCompletion (C : PrimitiveOracle) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) :
    localHistory ctx stack Q packet.val.profile
      (WHIRModeFinal.realHistory ctx Q C (completion ctx Q packet)) =
    WHIRModeReplay.history ctx stack Q packet (WHIRModeFinal.realCompletion ctx Q C (some packet)) := by
  have callers : (WHIRModeFinal.realCallers ctx Q C packet
      (WHIRModeFinal.callerPositions ctx Q packet)).filterMap (WHIRRawReplay.decodeEntry ctx stack Q) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro entry member
    obtain ⟨position,_,equal⟩ := List.mem_map.mp member
    subst entry
    rfl
  simp only [WHIRModeReplay.history,WHIRModeFinal.realCompletion,localHistory,
    WHIRRawReplay.decodeHistory,List.filterMap_append,callers,List.nil_append]
  rfl

theorem verifySource_completed_history (C : PrimitiveOracle) (cap : Nat)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q lanes : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (proofs : Array PrunedMerklePaths) (observations : List Observation) (v : Verified ctx Q cap packet)
    (answers : ∀ observation ∈ observations, observation.answer = realAnswer C ctx.iv observation.query)
    (run : Runs (WHIRSourceChronology.erase (verifySource cap model ctx stack Q lanes packet proofs))
      observations (some v)) :
    localHistory ctx stack Q packet.val.profile v.history =
      WHIRModeReplay.history ctx stack Q packet (WHIRModeFinal.realCompletion ctx Q C (some packet)) := by
  rw [verifySource_real_history C cap model ctx stack Q lanes packet proofs observations v answers run]
  exact local_realCompletion C ctx stack Q packet

/-- The accepted payload carries exactly the request decoded after the actual
caller prefix, not a second interpretation or an attacker-chosen claim object. -/
theorem verifySource_decoded_request (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q lanes : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (v : Verified ctx Q cap packet)
    (run : Runs (WHIRSourceChronology.erase (verifySource cap model ctx stack Q lanes packet proofs))
      observations (some v)) :
    ∃ before after, observations = before ++ after ∧
      before.map Observation.query = (WHIRModeFinal.callerPositions ctx Q packet).map
        (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property)) ∧
      WHIRCallerClaims.decodeAvailableRequest cap packet.val.profile lanes model.layout
        (RawWHIRKeys.entry ctx packet.val) (WHIRPhysicalCaller.latestAnswers before) = some v.request := by
  obtain ⟨root,before,after,request,_,_,trace,_,queries,decoded,physical⟩ :=
    WHIRPhysicalCaller.verifySource_success cap model ctx stack Q lanes packet proofs observations v run
  obtain ⟨wire,history,suffix,_,last⟩ := readPhysicalPackets_trace ctx stack Q packet.val.profile
    request.lanes proofs (completion ctx Q packet) (completion_profiles ctx Q packet)
    (initialWireState packet.val.profile root) _ after v physical
  have same := (WHIRPhysicalCaller.finish_success ctx Q cap packet request wire history _ _ v
    (done_result _ _ suffix last)).1
  exact ⟨before,after,trace,queries,by rw [same]; exact decoded⟩

theorem real_observation {cap : Nat} {R : Type} (registry : WHIRCallerRegistry.Public) (Q : Nat)
    (C : PrimitiveOracle) (source : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q source)
    (select : R → Option (RawWHIRKeys.Packet (WHIRCallerRegistry.context registry) Q))
    (whole : Counts Q (WHIRSourceBackfill.instrument (WHIRCallerRegistry.context registry) Q source select)) :
    WHIRObservableSource.observe registry Q select
      (runReal C registry.iv (WHIRSourceBackfill.instrument (WHIRCallerRegistry.context registry) Q source select)).view.result =
    some (WHIRObservableSource.tableObservation registry Q (WHIRRealSimulator.rawTable Q C) C source
      counted Q counted select) := by
  rw [WHIRRealSimulator.real_ideal_view C registry.iv _ whole]
  exact WHIRObservableSource.observe_ideal registry Q (WHIRRealSimulator.rawTable Q C) C source
    counted Q counted select whole

theorem real_observation_state {cap : Nat} {R : Type} (registry : WHIRCallerRegistry.Public) (Q : Nat)
    (C : PrimitiveOracle) (source : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q source)
    (select : R → Option (RawWHIRKeys.Packet (WHIRCallerRegistry.context registry) Q)) :
    (WHIRObservableSource.tableObservation registry Q (WHIRRealSimulator.rawTable Q C) C source
      counted Q counted select).state =
    WHIRSourceFrozenPrefix.replayState registry Q C source counted
      (WHIRSourceFrozenPrefix.allocationTrace registry Q select C source) := by
  change WHIRSourceFrozenPrefix.replayState registry Q C source counted
    (WHIRObservableSource.allocationTrace registry Q (WHIRRealSimulator.rawTable Q C) C source
      counted Q counted select) = _
  rw [show WHIRObservableSource.allocationTrace registry Q (WHIRRealSimulator.rawTable Q C) C source
      counted Q counted select = WHIRSourceFrozenPrefix.allocationTrace registry Q select C source from
    WHIRSourceFrozenPrefix.allocationTrace_compiler registry Q select C source counted Q counted]

/-- Canonical real completion and actual compiler cache completion describe the
same public failure event. No total oracle is added to the public observer. -/
theorem real_mode_failure_public {cap : Nat} {R : Type}
    (registry : WHIRCallerRegistry.Public) (Q : Nat) (C : PrimitiveOracle)
    (source : WHIRSourceChronology.Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (select : R → Option (RawWHIRKeys.Packet (WHIRCallerRegistry.context registry) Q))
    (whole : Counts Q (WHIRSourceBackfill.instrument (WHIRCallerRegistry.context registry) Q source select))
    (failed :
      let observed := WHIRObservableSource.tableObservation registry Q (WHIRRealSimulator.rawTable Q C)
        C source counted Q counted select
      let selected := select (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value
      WHIRModeReplay.Failure (WHIRCallerRegistry.context registry) rfl Q cap observed.state.catalog
        (CausalBindingState.roots observed.state) selected
        (WHIRModeFinal.realCompletion (WHIRCallerRegistry.context registry) Q C selected)) :
    WHIRObservableSource.Failure registry Q select
      (runReal C registry.iv (WHIRSourceBackfill.instrument (WHIRCallerRegistry.context registry) Q source select)).view.result := by
  let observed := WHIRObservableSource.tableObservation registry Q (WHIRRealSimulator.rawTable Q C)
    C source counted Q counted select
  have selected :
      WHIRObservableSource.selection registry Q select
        (tableExecution (WHIRCallerRegistry.context registry) Q (WHIRObservableSource.selection registry Q select)
          (WHIRObservableSource.rawProgram registry Q C source counted Q counted)
          (WHIRRealSimulator.rawTable Q C)).1 =
      select (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value := by
    rw [tableExecution_result,WHIRObservableSource.rawProgram_eval]
    change select (WHIRObservableSource.execution registry Q (WHIRRealSimulator.rawTable Q C)
      C source counted).view.result.value = _
    unfold WHIRObservableSource.execution
    rw [← WHIRRealSimulator.real_ideal_view C registry.iv _
      ((WHIRSourceChronology.compile_counted source Q).mpr counted)]
  have cached := (WHIRModeReplay.failure_iff_cache (WHIRCallerRegistry.context registry) rfl Q cap
    observed.state.catalog (CausalBindingState.roots observed.state)
    (WHIRObservableSource.selection registry Q select)
    (WHIRObservableSource.rawProgram registry Q C source counted Q counted)
    (WHIRRealSimulator.rawTable Q C)).mp (by
      rw [selected,← WHIRRealSimulator.realCompletion_ideal]
      exact failed)
  refine ⟨observed,real_observation registry Q C source counted select whole,?_⟩
  erw [WHIRSourceBackfill.real_result (WHIRCallerRegistry.context registry) Q C source select,← selected]
  exact cached

/-- End-to-end deterministic native coverage for the public production driver.
The attacker supplies only input bytes/proofs; the trusted native verifier runs
once. Its accepted false fixed-list claim forces either the public ROM failure
or an explicitly witnessed ordinary Merkle failure on the same full-C trace. -/
theorem nativeFailure_or_frozen (registry : WHIRPhysicalDriver.ProductionRegistry) (Q cap : Nat)
    (C : PrimitiveOracle) (attacker : WHIRSourceChronology.Source cap (WHIRPhysicalDriver.Unanchored.Input registry.context Q))
    (counted : WHIRSourceChronology.Counts Q (WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker))
    (whole : Counts Q (WHIRSourceBackfill.instrument registry.context Q
      (WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker) WHIRPhysicalDriver.Unanchored.select))
    (failed : WHIRNativeEvent.Failure registry Q
      (runReal C registry.iv (WHIRSourceBackfill.instrument registry.context Q
        (WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker) WHIRPhysicalDriver.Unanchored.select)).view.result) :
    WHIRObservableSource.Failure registry.publicRegistry Q WHIRPhysicalDriver.Unanchored.select
      (runReal C registry.iv (WHIRSourceBackfill.instrument registry.context Q
        (WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker) WHIRPhysicalDriver.Unanchored.select)).view.result ∨
    PublicMerkleProbability.FrozenOpeningBad C
      (WHIRSourceRootPolicy.policy registry.publicRegistry Q WHIRPhysicalDriver.Unanchored.select
        (WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker))
      (PublicCompressionProgram.primitiveLog C registry.iv (WHIRSourceBackfill.instrument registry.context Q
        (WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker) WHIRPhysicalDriver.Unanchored.select) Q whole) := by
  let source := WHIRPhysicalDriver.Unanchored.verifyAfter cap registry Q attacker
  let state := WHIRSourceFrozenPrefix.replayState registry.publicRegistry Q C source counted
    (WHIRSourceFrozenPrefix.allocationTrace registry.publicRegistry Q WHIRPhysicalDriver.Unanchored.select C source)
  have sourceResultEq := congrArg (fun output : WHIRNativeEvent.Output registry Q cap => output.result)
    (WHIRSourceBackfill.real_result registry.context Q C source WHIRPhysicalDriver.Unanchored.select)
  have observedEq := real_observation registry.publicRegistry Q C source counted WHIRPhysicalDriver.Unanchored.select whole
  obtain ⟨observed,seen,wrong⟩ := failed
  have same := Option.some.inj (seen.symm.trans observedEq)
  subst observed
  erw [real_observation_state,sourceResultEq] at wrong
  change WHIRPhysicalDriver.Unanchored.nativeWrong state
    (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value at wrong
  cases returned : (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value with
  | none =>
    rw [returned] at wrong
    exact False.elim wrong
  | some accepted =>
    rw [returned] at wrong
    obtain ⟨input,v,chosen,nativeReturned,acceptedEq,events⟩ :=
      WHIRPhysicalDriver.Unanchored.real_native_segment C registry.iv cap registry Q attacker accepted returned
    cases acceptedEq
    let nativeSource := verifySource cap (registry.packetModel Q input.packet) registry.context rfl Q
      (registry.packetLanes Q input.packet) input.packet input.proofs
    let nativeObs := WHIRSourceChronology.observations
      (runReal C registry.iv (WHIRSourceChronology.compile nativeSource)).view.result.events
    have nativeRun : Runs (WHIRSourceChronology.erase nativeSource) nativeObs (some v) := by
      have run := WHIRPhysicalCaller.real_source_runs C registry.iv nativeSource
      rw [nativeReturned] at run
      exact run
    have nativeAnswers : ∀ observation ∈ nativeObs,
        observation.answer = realAnswer C registry.iv observation.query := by
      intro observation member
      apply PublicMerkleProgram.runReal_answers C registry.iv (WHIRSourceChronology.compile nativeSource) observation
      rw [← WHIRSourceChronology.real_source_trace]
      exact member
    have nativeCounted : WHIRSourceChronology.Counts Q nativeSource := by
      have prefixRun := WHIRPhysicalCaller.real_source_runs C registry.iv attacker
      rw [← chosen] at prefixRun
      apply (WHIRSourceChronology.Source.map_counted nativeSource _ Q).mp
      exact WHIRSourceChronology.Source.bind_suffix_counted attacker
        (WHIRPhysicalDriver.Unanchored.verifier cap registry Q) Q _ input prefixRun counted
    have selected : WHIRPhysicalDriver.Unanchored.select
        (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value = some input.packet := by
      rw [returned]
      rfl
    obtain ⟨before,after,callerTrace,queries,decoded⟩ := verifySource_decoded_request cap
      (registry.packetModel Q input.packet) registry.context rfl Q (registry.packetLanes Q input.packet)
      input.packet input.proofs nativeObs v nativeRun
    have registeredDecode : WHIRCallerClaims.decodeAvailableRequest cap input.packet.val.profile
        (WHIRCallerClaims.callerLanes (WHIRCallerRegistry.packetLayout registry.publicRegistry Q input.packet))
        (WHIRCallerRegistry.packetLayout registry.publicRegistry Q input.packet)
        (WHIRRawReplay.callerEntry registry.context Q input.packet) (WHIRPhysicalCaller.latestAnswers before) = some v.request := by
      simpa only [WHIRPhysicalDriver.ProductionRegistry.packetLanes,registry.packetModel_layout,
        WHIRRawReplay.callerEntry] using decoded
    have captured := WHIRSourceCatalog.final_catalog_real registry.publicRegistry Q cap C source counted
      input.packet WHIRPhysicalDriver.Unanchored.select selected nativeSource nativeCounted before after callerTrace queries
      v.request registeredDecode
    have prepared := WHIRSourceCatalog.final_prepared_real registry.publicRegistry Q cap C source counted
      input.packet WHIRPhysicalDriver.Unanchored.select selected []
    obtain ⟨past,cursor,_⟩ := WHIRSourceFrozenPrefix.allocation_prefix_cursor registry.publicRegistry Q
      WHIRPhysicalDriver.Unanchored.select C source counted
      (WHIRSourceFrozenPrefix.allocationTrace registry.publicRegistry Q WHIRPhysicalDriver.Unanchored.select C source) []
      (by simp)
    have execution := verifySource_execution cap (registry.packetModel Q input.packet) registry.context rfl Q
      (registry.packetLanes Q input.packet) input.packet input.proofs nativeObs v nativeRun
    rcases trace_boundRows_or_bad C registry.iv input.packet input.proofs v nativeObs nativeAnswers
      execution.2 execution.1 state cursor.physical captured.2 prepared with bound | bad
    · left
      have found : WHIRRawROM.localCatalog state.catalog input.packet.val.profile
          (WHIRRawReplay.callerEntry registry.context Q input.packet) input.packet.val.statement =
          some (committedStatement v state) := by
        simp only [WHIRRawROM.localCatalog,WHIRRawReplay.callerEntry,RawWHIRKeys.entry,ite_true]
        exact captured.1
      have nativeFailed := verifySource_native_historyFailure cap (registry.packetModel Q input.packet)
        registry.context rfl Q (registry.packetLanes Q input.packet) input.packet input.proofs nativeObs v nativeRun
        state _ found bound wrong
      rw [verifySource_completed_history C cap (registry.packetModel Q input.packet) registry.context rfl Q
        (registry.packetLanes Q input.packet) input.packet input.proofs nativeObs v nativeAnswers nativeRun] at nativeFailed
      apply real_mode_failure_public registry.publicRegistry Q C source counted WHIRPhysicalDriver.Unanchored.select whole
      dsimp only
      erw [real_observation_state,selected]
      exact ⟨input.packet,rfl,nativeFailed⟩
    · right
      obtain ⟨opening,member,oldLog,frozen,bad⟩ := bad
      obtain ⟨snapshot,known⟩ := trace_opening_registered input.packet v.request.root
        (completion_chain registry.context Q input.packet) execution.1 state captured.2 prepared opening member
      obtain ⟨_,newLog,before,after,_,newFrozen,freeze,prior,ordinary,registered,_⟩ :=
        WHIRSourceFrozenPrefix.actual_backfill_retained registry.publicRegistry Q WHIRPhysicalDriver.Unanchored.select
          C source counted Q whole opening.root snapshot known
      have logs : oldLog = newLog := Option.some.inj (frozen.symm.trans newFrozen)
      subst newLog
      have nativeSubset : ∀ observation ∈ nativeObs,
          observation ∈ (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations := by
        intro observation present
        rw [← WHIRSourceChronology.real_source_trace,events,WHIRSourceChronology.observations_append]
        exact List.mem_append_right _ present
      have executed : ∀ n d, (⟨.primitive .verification n,d⟩ : Observation) ∈ nativeObs →
          (n,d) ∈ PublicCompressionProgram.primitiveLog C registry.iv
            (WHIRSourceBackfill.instrument registry.context Q source WHIRPhysicalDriver.Unanchored.select) Q whole := by
        intro n d present
        have expanded := WHIRSourceFrozenPrefix.primitive_expand C registry.iv
          (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations
          (PublicMerkleProgram.runReal_answers C registry.iv (WHIRSourceChronology.compile source))
          .verification n d (nativeSubset _ present)
        rw [WHIRSourceFrozenPrefix.expand_real C registry.iv (WHIRSourceChronology.compile source) Q
          ((WHIRSourceChronology.compile_counted source Q).mpr counted)] at expanded
        obtain ⟨suffix,equal⟩ := WHIRSourceFrozenPrefix.backfill_prefix registry.publicRegistry Q
          WHIRPhysicalDriver.Unanchored.select C source counted Q whole
        erw [← equal]
        exact List.mem_append_left suffix expanded
      exact observed_frozen_bad (execution.2 opening member) C registry.iv nativeAnswers _ _ before after oldLog
        freeze prior ordinary registered executed bad

end Whir.WHIRPhysicalBinding
