import Whir.WHIRPhysicalCaller
import Whir.WHIRSourceFrozenPrefix
import Whir.WHIRObservableSource

/-! The concrete source resolver's immutable catalog is obtained from actual
compiler allocations, including allocations caused by early raw prequeries.
Source annotations never install claims. A successful original caller forces
all allocations at its entry to decode the same request; consequently its first
registration cannot be a permanent rejection. -/
namespace Whir.WHIRSourceCatalog
open FiatShamirGame DuplexModeGame RawOracleCoupling RawOracleCoupling.Concrete
open WHIRCallerRegistry WHIRRawReplay CausalBindingState
open TypedOracleCompiler
open RawWHIRKeys (Packet)
set_option maxHeartbeats 1600000

variable {cap : Nat}

@[simp] theorem registerRoot_entries (s : State cap) (root : Digest32) :
    (registerRoot s root).entries = s.entries := by
  unfold registerRoot
  split <;> rfl

@[simp] theorem registerRoots_entries (s : State cap) (roots : List Digest32) :
    (registerRoots s roots).entries = s.entries := by
  induction roots generalizing s with
  | nil => rfl
  | cons root rest ih => exact (ih _).trans (registerRoot_entries s root)

@[simp] theorem observe_entries (s : State cap) (input : List Byte) (value : Digest32) :
    (observe s input value).entries = s.entries := by
  unfold observe
  split <;> rfl

@[simp] theorem observeRecords_entries (s : State cap) (records : MerkleTransport.Commitments.Records) :
    (WHIRSourceChronology.observeRecords s records).entries = s.entries := by
  induction records generalizing s with
  | nil => rfl
  | cons record rest ih => exact (ih _).trans (observe_entries _ _ _)

@[simp] theorem replayTracked_entries (s : State cap) (events : List (WHIRSourceChronology.Event cap)) :
    (WHIRSourceObserver.replayTracked s events).entries = s.entries := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
    unfold WHIRSourceObserver.replayTracked
    cases event with
    | answer query answer =>
      cases query with
      | primitive purpose input =>
        simp only [WHIRSourceChronology.step,ih,WHIRSourceChronology.observePublic,observeRecords_entries]
      | construction coordinate valid => exact ih s
    | commit root =>
      simp only [WHIRSourceChronology.step,ih,registerRoot_entries]
    | claims profile entry request =>
      cases h : MerkleTransport.Commitments.lookup request.root s.registry <;>
        simp only [WHIRSourceChronology.step,h,ih]

@[simp] theorem publicBefore_entries {R : Type} (registry : Public) (Q : Nat)
    (result : WHIRSourceChronology.Result cap R) (s : State cap) (key : AllocationKey (context registry) Q) :
    (WHIRSourceResolver.publicBefore registry Q result s key).state.entries = s.entries := by
  simp [WHIRSourceResolver.publicBefore,WHIRSourceObserver.publicReplay]

@[simp] theorem privateBefore_entries {R : Type} (registry : Public) (Q : Nat)
    (seed : DuplexPublicSimulator.Seed) (source : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q source) (s : State cap) (key : AllocationKey (context registry) Q) :
    (WHIRSourceResolver.privateBefore registry Q seed source counted s key).state.entries = s.entries := by
  simp [WHIRSourceResolver.privateBefore,WHIRSourceObserver.privateReplay]

@[simp] theorem after_entries (registry : Public) (Q : Nat) (s : State cap)
    (key : AllocationKey (context registry) Q) (answer : AllocationAnswer (context registry) Q key) :
    (WHIRSourceResolver.after registry Q s key answer).state.entries = s.entries := rfl

/-- A conditional invariant, proved below from the empty state rather than
assumed of a catalog. Its commitment is the original immutable root capture. -/
private def EntryCorrect (s : State cap) (p : ParameterBounds.Profile) (entry : FramedHistory)
    (request : ClaimRequest cap p) : Prop :=
  ∀ data, s.entries p entry = some data →
    data = some (bindClaims (capture s p request.root request.lanes request.lane_bound) request.claims) ∧
      ∃ snap, MerkleTransport.Commitments.lookup request.root s.registry = some snap

private theorem correct_transport {s t : State cap} (growth : Extends s t)
    (p : ParameterBounds.Profile) (entry : FramedHistory) (request : ClaimRequest cap p)
    (same : t.entries p entry = s.entries p entry) (correct : EntryCorrect s p entry request) :
    EntryCorrect t p entry request := by
  intro data found
  obtain ⟨equal,snap,known⟩ := correct data (same ▸ found)
  refine ⟨?_,snap,growth.registry _ _ known⟩
  rw [equal,capture_stable growth p request.root request.lanes request.lane_bound snap known]

private theorem prepareClaims_other (s : State cap) (p q : ParameterBounds.Profile)
    (entry other : FramedHistory) (key : StackWHIRReplay.Key q) (request : Option (ClaimRequest cap q))
    (different : q ≠ p ∨ other ≠ entry) :
    (prepareClaims s q other key request).1.entries p entry = s.entries p entry := by
  have registered (s : State cap) (data : Option (WHIRFiatShamir.StackInitial q cap)) :
      (registerStatement s q other data).entries p entry = s.entries p entry := by
    unfold registerStatement
    split
    · rfl
    · rcases different with profile | entered
      · simp [Function.update_of_ne (Ne.symm profile)]
      · by_cases profile : p = q
        · subst q
          simp [Function.update_of_ne (Ne.symm entered)]
        · simp [Function.update_of_ne profile]
  cases request <;>
    simp only [prepareClaims,prepare,registerFootprint,registerRoots_entries,registered,
      commit,registerRoot_entries]

private theorem prepareClaims_correct (s : State cap) (p : ParameterBounds.Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : ClaimRequest cap p)
    (correct : EntryCorrect s p entry request) :
    EntryCorrect (prepareClaims s p entry key (some request)).1 p entry request := by
  let committed := commit s p request.root request.lanes request.lane_bound
  let next := (prepareClaims s p entry key (some request)).1
  have growth : Extends committed.1 next := prepare_extends _ _ _ _ _
  have captureEq : committed.2 = capture next p request.root request.lanes request.lane_bound :=
    commit_persists s p request.root request.lanes request.lane_bound next growth
  have same : next.entries p entry = some (selected committed.1 p entry
      (some (bindClaims committed.2 request.claims))) :=
    (prepare committed.1 p entry key (some (bindClaims committed.2 request.claims))).2.found
  intro data found
  have dataEq := Option.some.inj (found.symm.trans same)
  cases old : s.entries p entry with
  | none =>
    have fresh : committed.1.entries p entry = none := by simpa [committed,commit] using old
    rw [dataEq,selected,fresh,Option.getD_none,captureEq]
    obtain ⟨snap,known⟩ := registerRoot_known s request.root
    exact ⟨rfl,snap,growth.registry _ _ known⟩
  | some previous =>
    have oldNext := (prepareClaims_extends s p entry key (some request)).entries p entry previous old
    have equal : previous = data := Option.some.inj (oldNext.symm.trans found)
    obtain ⟨value,snap,known⟩ := correct previous old
    rw [← equal]
    exact ⟨value.trans (congrArg (fun c => some (bindClaims c request.claims))
      (capture_stable (prepareClaims_extends s p entry key (some request)) p request.root
        request.lanes request.lane_bound snap known)),
      snap,(prepareClaims_extends s p entry key (some request)).registry _ _ known⟩

private theorem prepare_correct {R : Type} (registry : Public) (Q : Nat)
    (result : WHIRSourceChronology.Result cap R) (s : State cap)
    (p : ParameterBounds.Profile) (entry : FramedHistory) (request : ClaimRequest cap p)
    (key : AllocationKey (context registry) Q)
    (agrees : ∀ packet, key.1 = .inl packet → packet.val.profile = p →
      callerEntry (context registry) Q packet = entry →
      HEq (packetRequest registry Q cap packet key.2) (some request))
    (correct : EntryCorrect s p entry request) :
    EntryCorrect (WHIRCausalRawROM.prepare (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result) s key).1 p entry request := by
  let prior := (WHIRSourceResolver.publicBefore registry Q result s key).state
  have priorCorrect : EntryCorrect prior p entry request :=
    correct_transport (WHIRSourceResolver.publicBefore registry Q result s key).growth p entry request
      (congrFun (congrFun (publicBefore_entries registry Q result s key) p) entry) correct
  rcases key with ⟨group,history⟩
  cases group with
  | inr raw => exact priorCorrect
  | inl packet =>
    change EntryCorrect (prepareClaims prior packet.val.profile (callerEntry (context registry) Q packet)
      (localKey (allocationKey (context registry) rfl Q packet history))
      (packetRequest registry Q cap packet history)).1 p entry request
    by_cases profile : packet.val.profile = p
    · subst p
      by_cases entered : callerEntry (context registry) Q packet = entry
      · have equal := eq_of_heq (agrees packet rfl rfl entered)
        rw [equal,entered]
        exact prepareClaims_correct prior _ entry _ request priorCorrect
      · exact correct_transport (prepareClaims_extends ..) _ _ _
          (prepareClaims_other _ _ _ _ _ _ _ (Or.inr entered)) priorCorrect
    · exact correct_transport (prepareClaims_extends ..) _ _ _
        (prepareClaims_other _ _ _ _ _ _ _ (Or.inl profile)) priorCorrect

private theorem evolution_correct {R : Type} (registry : Public) (Q : Nat)
    (result : WHIRSourceChronology.Result cap R)
    (p : ParameterBounds.Profile) (entry : FramedHistory) (request : ClaimRequest cap p)
    {s final : State cap} {raw labeled}
    (evolution : (WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result)).Evolves s raw labeled final)
    (agrees : ∀ allocation ∈ raw, ∀ packet, allocation.1.1 = .inl packet → packet.val.profile = p →
      callerEntry (context registry) Q packet = entry →
      HEq (packetRequest registry Q cap packet allocation.1.2) (some request))
    (correct : EntryCorrect s p entry request) : EntryCorrect final p entry request := by
  induction evolution with
  | nil => exact correct
  | cons s key answer tail ih =>
    apply ih (fun allocation member => agrees allocation (List.mem_cons_of_mem _ member))
    have prepared := prepare_correct registry Q result s p entry request key
      (agrees ⟨key,answer⟩ List.mem_cons_self) correct
    rcases key with ⟨group,history⟩
    cases group <;> exact prepared

private theorem prepareClaims_registered (s : State cap) (p : ParameterBounds.Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) :
    ∃ data, (prepareClaims s p entry key request).1.entries p entry = some data := by
  cases request with
  | none => exact ⟨_,(prepare s p entry key none).2.found⟩
  | some request => exact ⟨_,(prepare (commit s p request.root request.lanes request.lane_bound).1
      p entry key (some (bindClaims (commit s p request.root request.lanes request.lane_bound).2 request.claims))).2.found⟩

private theorem evolution_registered {R : Type} (registry : Public) (Q : Nat)
    (result : WHIRSourceChronology.Result cap R) {s final : State cap} {raw labeled}
    (evolution : (WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result)).Evolves s raw labeled final)
    (allocation : Sigma (AllocationAnswer (context registry) Q)) (member : allocation ∈ raw)
    (packet : Packet (context registry) Q) (packetKey : allocation.1.1 = .inl packet) :
    ∃ data, final.entries packet.val.profile (callerEntry (context registry) Q packet) = some data := by
  induction evolution with
  | nil => cases member
  | cons s key answer tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst allocation
      rcases key with ⟨group,history⟩
      dsimp only at packetKey
      subst group
      let built := WHIRCausalRawROM.prepare (context registry) rfl Q cap
        (WHIRSourceResolver.publicResolver registry Q result) s (.inl packet,history)
      have growth := (WHIRSourceResolver.after registry Q built.1 (.inl packet,history) answer).growth.trans
        (WHIRCausalRawROM.evolution_extends (context registry) rfl Q cap
          (WHIRSourceResolver.publicResolver registry Q result) tail)
      obtain ⟨data,found⟩ := prepareClaims_registered
        (WHIRSourceResolver.publicBefore registry Q result s (.inl packet,history)).state
        packet.val.profile (callerEntry (context registry) Q packet)
        (localKey (allocationKey (context registry) rfl Q packet history))
        (packetRequest registry Q cap packet history)
      exact ⟨data,growth.entries _ _ _ found⟩
    · exact ih member

/-- Every actual allocation at the same entry uses the same complete warmed
caller dependencies, even if an early raw prequery caused its allocation. -/
theorem allocation_request {R : Type} {K : Nat}
    (registry : Public) (Q cap : Nat) (target packet : Packet (context registry) Q)
    (select : R → Option (Packet (context registry) Q))
    (program : Sampling (RawKey Q) (fun _ => Digest32) R K) (table : RawKey Q → Digest32)
    (allocation : Sigma (AllocationAnswer (context registry) Q))
    (member : allocation ∈ (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q table)
      (compile (context registry) Q select program)).2)
    (key : allocation.1.1 = .inl packet)
    (same : callerEntry (context registry) Q packet = callerEntry (context registry) Q target)
    (original : Sigma (AllocationAnswer (context registry) Q))
    (originalMember : original ∈ (Sampling.execute
      (WHIRObservableAllocations.allocationOracle (context registry) Q table)
      (compile (context registry) Q select program)).2)
    (originalKey : original.1.1 = .inl target)
    (request : ClaimRequest cap target.val.profile)
    (decoded : packetRequest registry Q cap target original.1.2 = some request) :
    HEq (packetRequest registry Q cap packet allocation.1.2) (some request) := by
  have equal := packetRequest_same_entry registry Q cap packet target allocation.1.2 original.1.2 same (by
    intro q prior
    rw [callerAnswers_table_compile select program table allocation member packet key,
      callerAnswers_table_compile select program table original originalMember target originalKey]
    have targetPrior : q ∈ WHIRCallerOutputs.callerOutputs (callerEntry (context registry) Q target) := same ▸ prior
    change q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry (context registry) target.val) at targetPrior
    simp only [tableCallerAnswers,dite_eq_left prior,dite_eq_left targetPrior]
    rfl)
  rw [decoded] at equal
  exact equal

/-- Final-catalog existence and unchanged original claims, derived from the
actual compiler's recorded selected packet and causal execution from empty.
No first-registration, catalog consistency, or decoder agreement is assumed. -/
theorem final_catalog {R S T Seed SimState : Type} {K : Nat}
    (registry : Public) (Q cap : Nat) (result : WHIRSourceChronology.Result cap T)
    (target : Packet (context registry) Q) (select : R → Option (Packet (context registry) Q))
    (program : Sampling (RawKey Q) (fun _ => Digest32) R K) (table : RawKey Q → Digest32)
    (selected : select (tableExecution (context registry) Q select program table).1 = some target)
    (sim : Simulator Q Seed SimState) (state : SimState) (source : WHIRSourceChronology.Source cap S)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : WHIRSourceChronology.Counts remaining source)
    (before after : List Observation)
    (sourcePrefix : WHIRSourceChronology.observations
      (runIdeal sim table (context registry).iv state (WHIRSourceChronology.compile source) remaining limit
        ((WHIRSourceChronology.compile_counted source remaining).mpr counted)).view.result.events = before ++ after)
    (queries : before.map Observation.query = (WHIRModeFinal.callerPositions (context registry) Q target).map
      (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible (context registry) Q target q.val q.property)))
    (request : ClaimRequest cap target.val.profile)
    (decoded : WHIRCallerClaims.decodeAvailableRequest cap target.val.profile
      (WHIRCallerClaims.callerLanes (packetLayout registry Q target)) (packetLayout registry Q target)
      (callerEntry (context registry) Q target) (WHIRPhysicalCaller.latestAnswers before) = some request) :
    let trace := (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q table)
      (compile (context registry) Q select program)).2
    let final := ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result)).traceRecode (empty cap) trace).2
    final.catalog target.val.profile (callerEntry (context registry) Q target) =
      some (bindClaims (capture final target.val.profile request.root request.lanes request.lane_bound) request.claims) ∧
    ∃ snap, MerkleTransport.Commitments.lookup request.root final.registry = some snap := by
  dsimp only
  let trace := (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q table)
    (compile (context registry) Q select program)).2
  have run := Sampling.execute_runs (WHIRObservableAllocations.allocationOracle (context registry) Q table)
    (compile (context registry) Q select program)
  rw [WHIRObservableAllocations.compile_cache] at run
  obtain ⟨cached,recorded⟩ := recorded (context registry) Q select program run
  rw [selected] at cached
  obtain ⟨answer,hit⟩ := cached target (by simp [terminalCompletion,completion])
  have member := (recorded (.inl target) answer hit).2
  have selectedRequest := (WHIRPhysicalCaller.packetRequest_compiled_prefix registry Q cap target
    select program table _ member rfl sim state source remaining limit counted before after sourcePrefix queries).trans decoded
  have evolution := (WHIRCausalRawROM.decorator (context registry) rfl Q cap
    (WHIRSourceResolver.publicResolver registry Q result)).traceRecode_evolves (empty cap) trace
  obtain ⟨data,found⟩ := evolution_registered registry Q result evolution _ member target rfl
  have correct := evolution_correct registry Q result target.val.profile
    (callerEntry (context registry) Q target) request evolution (by
      intro allocation member packet key _ same
      exact allocation_request registry Q cap target packet select program table allocation member key same
        _ (recorded (.inl target) answer hit).2 rfl request selectedRequest)
    (by intro data found; cases found)
  obtain ⟨equal,known⟩ := correct data found
  refine ⟨?_,known⟩
  change (((WHIRCausalRawROM.decorator (context registry) rfl Q cap
    (WHIRSourceResolver.publicResolver registry Q result)).traceRecode (empty cap) trace).2.entries
      target.val.profile (callerEntry (context registry) Q target)).getD none = _
  rw [found,Option.getD_some,equal]

private theorem prepareClaims_prepared (s : State cap) (p : ParameterBounds.Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) :
    Prepared (prepareClaims s p entry key request).1 p key := by
  cases request with
  | none => exact (prepare s p entry key none).2.prepared
  | some request => exact (prepare (commit s p request.root request.lanes request.lane_bound).1
      p entry key (some (bindClaims (commit s p request.root request.lanes request.lane_bound).2 request.claims))).2.prepared

private theorem evolution_prepared {R : Type} (registry : Public) (Q : Nat)
    (result : WHIRSourceChronology.Result cap R) {s final : State cap} {raw labeled}
    (evolution : (WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result)).Evolves s raw labeled final)
    (allocation : Sigma (AllocationAnswer (context registry) Q)) (member : allocation ∈ raw)
    (packet : Packet (context registry) Q) (packetKey : allocation.1.1 = .inl packet)
    (past : List (LocalEntry packet.val.profile)) :
    Prepared final packet.val.profile ⟨packet.val.statement,packet.val.messages,past⟩ := by
  induction evolution with
  | nil => cases member
  | cons s key answer tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst allocation
      rcases key with ⟨group,history⟩
      dsimp only at packetKey
      subst group
      let built := WHIRCausalRawROM.prepare (context registry) rfl Q cap
        (WHIRSourceResolver.publicResolver registry Q result) s (.inl packet,history)
      have growth := (WHIRSourceResolver.after registry Q built.1 (.inl packet,history) answer).growth.trans
        (WHIRCausalRawROM.evolution_extends (context registry) rfl Q cap
          (WHIRSourceResolver.publicResolver registry Q result) tail)
      have prepared := prepareClaims_prepared
        (WHIRSourceResolver.publicBefore registry Q result s (.inl packet,history)).state
        packet.val.profile (callerEntry (context registry) Q packet)
        (localKey (allocationKey (context registry) rfl Q packet history))
        (packetRequest registry Q cap packet history)
      intro ref member
      obtain ⟨snap,known⟩ := prepared ref member
      exact ⟨snap,growth.registry _ _ known⟩
    · exact ih member

/-- Every root in the selected packet's actual history footprint is registered
in the final causal state. Compiler completion and recorded allocation supply
the witness; neither accepted-catalog nor root-coverage assumptions are needed.
Past answers are arbitrary because preparation depends only on the original
statement and messages, not the supplied replay ancestors. -/
theorem final_prepared {R T : Type} {K : Nat}
    (registry : Public) (Q cap : Nat) (result : WHIRSourceChronology.Result cap T)
    (target : Packet (context registry) Q) (select : R → Option (Packet (context registry) Q))
    (program : Sampling (RawKey Q) (fun _ => Digest32) R K) (table : RawKey Q → Digest32)
    (selected : select (tableExecution (context registry) Q select program table).1 = some target)
    (past : List (LocalEntry target.val.profile)) :
    let trace := (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q table)
      (compile (context registry) Q select program)).2
    let final := ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result)).traceRecode (empty cap) trace).2
    Prepared final target.val.profile ⟨target.val.statement,target.val.messages,past⟩ := by
  have run := Sampling.execute_runs (WHIRObservableAllocations.allocationOracle (context registry) Q table)
    (compile (context registry) Q select program)
  rw [WHIRObservableAllocations.compile_cache] at run
  obtain ⟨cached,recorded⟩ := recorded (context registry) Q select program run
  rw [selected] at cached
  obtain ⟨answer,hit⟩ := cached target (by simp [terminalCompletion,completion])
  exact evolution_prepared registry Q result
    ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q result)).traceRecode_evolves (empty cap) _)
    _ (recorded (.inl target) answer hit).2 target rfl past

private theorem real_selected {R : Type} (registry : Public) (Q cap : Nat)
    (C : PrimitiveOracle) (source : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q source)
    (target : Packet (context registry) Q) (select : R → Option (Packet (context registry) Q))
    (selected : select (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value = some target) :
    WHIRObservableSource.selection registry Q select
      (tableExecution (context registry) Q (WHIRObservableSource.selection registry Q select)
        (WHIRObservableSource.rawProgram registry Q C source counted Q counted)
        (WHIRRealSimulator.rawTable Q C)).1 = some target := by
  rw [tableExecution_result,WHIRObservableSource.rawProgram_eval]
  change select (WHIRObservableSource.execution registry Q (WHIRRealSimulator.rawTable Q C)
    C source counted).view.result.value = some target
  unfold WHIRObservableSource.execution
  rw [← WHIRRealSimulator.real_ideal_view C registry.iv _ ((WHIRSourceChronology.compile_counted source Q).mpr counted)]
  exact selected

/-- Real-execution catalog specialization. The original native caller prefix
and decoder equation are operational certificates; the actual full source
determines the allocation path and selected packet without catalog assumptions. -/
theorem final_catalog_real {R S : Type}
    (registry : Public) (Q cap : Nat) (C : PrimitiveOracle)
    (fullSource : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q fullSource)
    (target : Packet (context registry) Q) (select : R → Option (Packet (context registry) Q))
    (selected : select (runReal C registry.iv (WHIRSourceChronology.compile fullSource)).view.result.value = some target)
    (nativeSource : WHIRSourceChronology.Source cap S)
    (nativeCounted : WHIRSourceChronology.Counts Q nativeSource)
    (before after : List Observation)
    (sourcePrefix : WHIRSourceChronology.observations
      (runReal C registry.iv (WHIRSourceChronology.compile nativeSource)).view.result.events = before ++ after)
    (queries : before.map Observation.query = (WHIRModeFinal.callerPositions (context registry) Q target).map
      (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible (context registry) Q target q.val q.property)))
    (request : ClaimRequest cap target.val.profile)
    (decoded : WHIRCallerClaims.decodeAvailableRequest cap target.val.profile
      (WHIRCallerClaims.callerLanes (packetLayout registry Q target)) (packetLayout registry Q target)
      (callerEntry (context registry) Q target) (WHIRPhysicalCaller.latestAnswers before) = some request) :
    let final := WHIRSourceFrozenPrefix.replayState registry Q C fullSource counted
      (WHIRSourceFrozenPrefix.allocationTrace registry Q select C fullSource)
    final.catalog target.val.profile (callerEntry (context registry) Q target) =
      some (bindClaims (capture final target.val.profile request.root request.lanes request.lane_bound) request.claims) ∧
    ∃ snap, MerkleTransport.Commitments.lookup request.root final.registry = some snap := by
  have idealPrefix : WHIRSourceChronology.observations
      (runIdeal (DuplexPublicSimulator.simulator Q) (WHIRRealSimulator.rawTable Q C) (context registry).iv
        ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile nativeSource)
        Q (Nat.le_refl Q) ((WHIRSourceChronology.compile_counted nativeSource Q).mpr nativeCounted)).view.result.events =
      before ++ after := by
    rw [← WHIRRealSimulator.real_ideal_view C (context registry).iv _ ((WHIRSourceChronology.compile_counted nativeSource Q).mpr nativeCounted)]
    exact sourcePrefix
  have result := final_catalog registry Q cap
    (runReal C registry.iv (WHIRSourceChronology.compile fullSource)).view.result target
    (WHIRObservableSource.selection registry Q select)
    (WHIRObservableSource.rawProgram registry Q C fullSource counted Q counted)
    (WHIRRealSimulator.rawTable Q C) (real_selected registry Q cap C fullSource counted target select selected)
    (DuplexPublicSimulator.simulator Q) ((DuplexPublicSimulator.simulator Q).initial C)
    nativeSource Q (Nat.le_refl Q) nativeCounted before after idealPrefix queries request decoded
  have traceEq :
      (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q (WHIRRealSimulator.rawTable Q C))
        (compile (context registry) Q (WHIRObservableSource.selection registry Q select)
          (WHIRObservableSource.rawProgram registry Q C fullSource counted Q counted))).2 =
      WHIRSourceFrozenPrefix.allocationTrace registry Q select C fullSource :=
    WHIRSourceFrozenPrefix.allocationTrace_compiler registry Q select C fullSource counted Q counted
  dsimp only at result
  rw [traceEq,WHIRSourceFrozenPrefix.public_replayState] at result
  exact result

/-- Real full-source execution registers the entire selected packet footprint;
the lookup witnesses come from compiler preparation, even for early prequeries. -/
theorem final_prepared_real {R : Type}
    (registry : Public) (Q cap : Nat) (C : PrimitiveOracle)
    (fullSource : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q fullSource)
    (target : Packet (context registry) Q) (select : R → Option (Packet (context registry) Q))
    (selected : select (runReal C registry.iv (WHIRSourceChronology.compile fullSource)).view.result.value = some target)
    (past : List (LocalEntry target.val.profile)) :
    let final := WHIRSourceFrozenPrefix.replayState registry Q C fullSource counted
      (WHIRSourceFrozenPrefix.allocationTrace registry Q select C fullSource)
    Prepared final target.val.profile ⟨target.val.statement,target.val.messages,past⟩ := by
  have result := final_prepared registry Q cap
    (runReal C registry.iv (WHIRSourceChronology.compile fullSource)).view.result target
    (WHIRObservableSource.selection registry Q select)
    (WHIRObservableSource.rawProgram registry Q C fullSource counted Q counted)
    (WHIRRealSimulator.rawTable Q C) (real_selected registry Q cap C fullSource counted target select selected) past
  have traceEq :
      (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q (WHIRRealSimulator.rawTable Q C))
        (compile (context registry) Q (WHIRObservableSource.selection registry Q select)
          (WHIRObservableSource.rawProgram registry Q C fullSource counted Q counted))).2 =
      WHIRSourceFrozenPrefix.allocationTrace registry Q select C fullSource :=
    WHIRSourceFrozenPrefix.allocationTrace_compiler registry Q select C fullSource counted Q counted
  dsimp only at result
  rw [traceEq,WHIRSourceFrozenPrefix.public_replayState] at result
  exact result

end Whir.WHIRSourceCatalog
