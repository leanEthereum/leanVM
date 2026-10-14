import Whir.PCSBCSNativePhysicalFreeze
import Whir.PCSBCSNativeCapturedTape
import Whir.PCSBCSNativeRootRoles

/-! Whole historical native packet provenance. Attacker prequeries remain in the
allocation program; construction answers retain every byte of every block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSWholeNativePacketCoverage
open Concrete Protocol FiatShamirGame DuplexModeGame DuplexFraming TypedOracleCompiler
open PublicMerkleProgram WHIRSourceChronology WHIRPhysicalVerifier WHIRPhysicalReplay
open RawOracleCoupling.Concrete CausalProbability PCSBCSChallengeOracle
open MerkleTransport MerkleTransport.Commitments PCSBCSRestorationHazard
open PCSRoundByRoundTranscriptState
open PCSBCSNativeCapturedTape
open PCSBCSNativePhysicalFreeze (wholeProgram allocationProgram actualTable)

noncomputable abbrev mixedTable {p : ParameterBounds.Profile} {B boundary : Nat} {iv : Digest32}
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :=
  (EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)).split
    (PublicCompressionCouplingMixed.oracle seed ro)

/-- Literal equality of full source blocks, before any scalar or query-index
projection. The last block's unused high suffix is part of this equality. -/
theorem fullWidth_of_answers (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q B : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B)
    {p : ParameterBounds.Profile} {entry : FramedHistory}
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (raw : GroupAnswer ctx Q (.inl packet))
    (answers : ∀ b : Fin (RawWHIRKeys.blocks ctx packet.val),
      ∃ bound : pathCost (RawWHIRKeys.coordinate ctx packet.val b.val) ≤ B,
        raw b = ro (constructionKey B ctx.iv (RawWHIRKeys.coordinate ctx packet.val b.val) bound)) :
    let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
    let current := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B packetB profile aligned
    HEq (mixedTable seed ro (.inl current))
      (PCSBCSNativePacketCodec.nativeFullBlocksEquiv ctx stack B packetB raw) := by
  cases profile
  cases aligned
  let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
  apply heq_of_eq
  funext b
  change ro ((PCSBCSNativePacketBridge.sourcePacket ctx stack B packetB).key b) = _
  rw [PCSBCSNativePacketBridge.sourcePacket_key,PCSBCSNativePacketCodec.nativeFullBlocksEquiv_apply]
  obtain ⟨bound,equal⟩ := answers ⟨b.val,by
    change b.val < RawWHIRKeys.blocks ctx packetB.val
    rw [PCSBCSNativePacketBridge.packet_blocks_pcs ctx stack B packetB]
    exact b.isLt⟩
  exact equal.symm

section Whole
variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)
    (attacker : Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (A B : Nat) (limit : A ≤ B) (counted : DuplexModeGame.Counts A (wholeProgram cap registry Q attacker))
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

noncomputable abbrev mixedView :=
  Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
    (PublicCompressionCouplingMixed.compile B registry.context.iv []
      (wholeProgram cap registry Q attacker) A limit counted)

theorem allocationView_mixed (p : ParameterBounds.Profile) (boundary : Nat) :
    Sampling.eval (mixedTable (p := p) (iv := registry.context.iv) (boundary := boundary) seed ro)
      (allocationProgram (p := p) (boundary := boundary)
        (wholeProgram cap registry Q attacker) A limit counted) =
      mixedView cap registry Q attacker A B limit counted seed ro := by
  rw [Atomic.eval_program,RawOracleCoupling.Partition.join_split]

 theorem mixedView_runs :
    Runs (erase (AnchoredPhysicalAfter.verifyAfter cap registry Q attacker))
      (mixedView cap registry Q attacker A B limit counted seed ro).observations
      (mixedView cap registry Q attacker A B limit counted seed ro).result.value ∧
    WHIRSourceChronology.observations
      (mixedView cap registry Q attacker A B limit counted seed ro).result.events =
      (mixedView cap registry Q attacker A B limit counted seed ro).observations ∧
    AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed
      (mixedView cap registry Q attacker A B limit counted seed ro).observations := by
  have run : Runs (wholeProgram cap registry Q attacker)
      (mixedView cap registry Q attacker A B limit counted seed ro).observations
      (mixedView cap registry Q attacker A B limit counted seed ro).result := by
    simp only [mixedView,PublicCompressionCouplingMixed.compile_actual]
    exact runIdeal_runs (DuplexPublicSimulator.simulator B) ro registry.context.iv
      ⟨seed,[]⟩ _ A limit counted
  obtain ⟨erased,observed⟩ := WHIRPhysicalCaller.compile_run
    (AnchoredPhysicalAfter.verifyAfter cap registry Q attacker) _ _ run
  refine ⟨erased,observed,?_⟩
  simpa only [AnchoredIdealPhysicalAcceptance.PrimitiveConsistent,mixedView,
    PublicCompressionCouplingMixed.compile_actual,DuplexPublicSimulator.simulator] using
    PCSBCSMixedOrdinaryMerkle.runIdeal_initial_answers B seed ro registry.context.iv
      (wholeProgram cap registry Q attacker) A limit counted

 theorem mixed_success_native_segment (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∃ before after,
      (mixedView cap registry Q attacker A B limit counted seed ro).observations = before ++ after ∧
      Runs (erase attacker) before a.input ∧
      Runs (erase (AnchoredPhysicalDriver.verifySource cap .fresh
        (registry.packetModel Q a.input.packet) registry.context rfl Q
        a.input.packet a.input.record a.input.proofs)) after (some a.native) ∧
      AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed after := by
  obtain ⟨run,_,consistent⟩ := mixedView_runs cap registry Q attacker A B limit counted seed ro
  rw [success] at run
  obtain ⟨input,before,after,native,split,first,last,equal⟩ :=
    AnchoredPhysicalAfter.native_segment cap registry Q attacker _ a run
  cases equal
  refine ⟨before,after,split,first,last,?_⟩
  intro o member ordinary
  apply consistent o _ ordinary
  rw [split]
  exact List.mem_append_right _ member

 theorem mixed_success_recorded (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∀ current (member : current ∈ completion registry.context Q a.input.packet),
      ∃ bounded : pathCost (RawWHIRKeys.coordinate registry.context current.val 0) ≤ B,
        let entered := PCSBCSNativePacketBridge.enteredPacketAt registry.context rfl B
          (PCSBCSNativePacketVisit.packetAtBound registry.context Q B current bounded)
          (completion_profiles registry.context Q a.input.packet current member)
          (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
        (⟨.inl entered,mixedTable seed ro (.inl entered)⟩ : Sigma PCSBCSSourceRootCapture.Answer) ∈
          (Sampling.execute (mixedTable seed ro)
            (allocationProgram (p := a.input.packet.val.profile)
              (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
              (wholeProgram cap registry Q attacker) A limit counted)).2 := by
  obtain ⟨before,after,split,_,nativeRun,_⟩ := mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  intro current member
  obtain ⟨answer,queried⟩ := PCSBCSNativePacketVisit.verifySource_queried
    cap .fresh (registry.packetModel Q a.input.packet) registry.context rfl Q
    a.input.packet a.input.record a.input.proofs after a.native nativeRun current member
  apply PCSBCSNativePacketVisit.observed_packet_recorded registry.context rfl Q B current
    (completion_profiles registry.context Q a.input.packet current member)
    (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
    seed ro [] (wholeProgram cap registry Q attacker) A limit counted answer
  have present : (⟨WHIRModeFinal.request registry.context Q current
      ⟨0,RawWHIRKeys.blocks_positive registry.context current.val⟩,answer⟩ : Observation) ∈
      (mixedView cap registry Q attacker A B limit counted seed ro).observations := by
    rw [split]
    exact List.mem_append_right _ queried
  simpa only [mixedView,PublicCompressionCouplingMixed.compile_actual] using present

 theorem mixed_success_depth (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    a.input.packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config a.input.packet.val.profile) := by
  obtain ⟨_,after,_,_,run,_⟩ := mixed_success_native_segment cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution cap .fresh
    (registry.packetModel Q a.input.packet) registry.context rfl Q
    a.input.packet a.input.record a.input.proofs after a.native run
  exact AnchoredPhysicalPreparation.accepted_completed_depth a.native
    (trace_completed a.input.record.root (completion_chain registry.context Q a.input.packet) trace)


/-- The actual accepted history contains each scheduled packet, and every full
block of those actual answers is the whole runner's literal raw-table answer. -/
theorem mixed_success_full_answers (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    Trace registry.context rfl Q a.input.packet.val.profile a.input.record.shape.lanes
      a.input.proofs (completion registry.context Q a.input.packet)
      (initialWireState a.input.packet.val.profile a.input.record.root) a.native.wire a.native.history ∧
    (∀ current ∈ completion registry.context Q a.input.packet,
      ∃ raw, (⟨.inl current,raw⟩ : Sigma (GroupAnswer registry.context Q)) ∈ a.native.history) ∧
    (∀ (current : RawWHIRKeys.Packet registry.context Q) (raw : GroupAnswer registry.context Q (.inl current)),
      (⟨.inl current,raw⟩ : Sigma (GroupAnswer registry.context Q)) ∈ a.native.history →
      ∀ b : Fin (RawWHIRKeys.blocks registry.context current.val),
        ∃ bound : pathCost (RawWHIRKeys.coordinate registry.context current.val b.val) ≤ B,
        raw b = ro (constructionKey B registry.context.iv
          (RawWHIRKeys.coordinate registry.context current.val b.val) bound)) := by
  obtain ⟨before,after,split,_,run,_⟩ := mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨configured,same,prior,physical,request,whole,_,_,_,physicalRun⟩ :=
    AnchoredPhysicalExecution.verifySource_success cap .fresh (registry.packetModel Q a.input.packet)
      registry.context rfl Q a.input.packet a.input.record a.input.proofs after a.native run
  obtain ⟨final,history,suffix,trace,last,observed⟩ := readPackets_observed registry.context rfl Q
    a.input.packet.val.profile a.input.record.shape.lanes a.input.proofs _ _ _ _ physical a.native physicalRun
  obtain ⟨_,wireEq,historyEq⟩ := AnchoredPhysicalExecution.finish_success registry.context Q cap
    a.input.packet a.input.record configured request final history _ a.native (done_eq last)
  have traced : Trace registry.context rfl Q a.input.packet.val.profile a.input.record.shape.lanes
      a.input.proofs (completion registry.context Q a.input.packet)
      (initialWireState a.input.packet.val.profile a.input.record.root) a.native.wire a.native.history := by
    simpa only [← wireEq,← historyEq] using trace
  refine ⟨traced,trace_answers traced,?_⟩
  intro current raw member b
  apply PCSBCSIdealConstructionAnswers.construction_observations (DuplexPublicSimulator.simulator B)
    ro registry.context.iv ⟨seed,[]⟩ (wholeProgram cap registry Q attacker) A limit counted
    _ _ (raw b)
  have present : (⟨WHIRModeFinal.request registry.context Q current b,raw b⟩ : Observation) ∈
      (mixedView cap registry Q attacker A B limit counted seed ro).observations := by
    rw [split,whole]
    exact List.mem_append_right _ (List.mem_append_right _
      (observed current raw (by simpa only [historyEq] using member) b))
  simpa only [mixedView,PublicCompressionCouplingMixed.compile_actual,WHIRModeFinal.request] using present

/-- Each scheduled whole allocation has the actual native full-width answer,
with its literal canonical entry and messages; visitation is also derived. -/
theorem mixed_success_fullWidth_packets (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∀ current (member : current ∈ completion registry.context Q a.input.packet),
      ∃ raw : GroupAnswer registry.context Q (.inl current),
        ∃ bounded : pathCost (RawWHIRKeys.coordinate registry.context current.val 0) ≤ B,
          let packetB := PCSBCSNativePacketVisit.packetAtBound registry.context Q B current bounded
          let entered := PCSBCSNativePacketBridge.enteredPacketAt registry.context rfl B packetB
            (completion_profiles registry.context Q a.input.packet current member)
            (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
          (⟨.inl current,raw⟩ : Sigma (GroupAnswer registry.context Q)) ∈ a.native.history ∧
          HEq (mixedTable seed ro (.inl entered))
            (PCSBCSNativePacketCodec.nativeFullBlocksEquiv registry.context rfl B packetB raw) ∧
          (⟨.inl entered,mixedTable seed ro (.inl entered)⟩ : Sigma PCSBCSSourceRootCapture.Answer) ∈
            (Sampling.execute (mixedTable seed ro)
              (allocationProgram (p := a.input.packet.val.profile)
                (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
                (wholeProgram cap registry Q attacker) A limit counted)).2 := by
  obtain ⟨_,answers,blocks⟩ := mixed_success_full_answers cap registry Q attacker A B limit counted seed ro a success
  intro current member
  obtain ⟨raw,inHistory⟩ := answers current member
  obtain ⟨bounded,recorded⟩ := mixed_success_recorded cap registry Q attacker A B limit counted seed ro a success current member
  exact ⟨raw,bounded,inHistory,fullWidth_of_answers registry.context rfl Q B current bounded
    (completion_profiles registry.context Q a.input.packet current member)
    (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
    seed ro raw (blocks current raw inHistory),recorded⟩

theorem mixed_success_literal_packets (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∃ initial, a.native.wire.initial = some initial ∧
      ∀ current (member : current ∈ completion registry.context Q a.input.packet),
        ∃ bounded : pathCost (RawWHIRKeys.coordinate registry.context current.val 0) ≤ B,
          let entered := PCSBCSNativePacketBridge.enteredPacketAt registry.context rfl B
            (PCSBCSNativePacketVisit.packetAtBound registry.context Q B current bounded)
            (completion_profiles registry.context Q a.input.packet current member)
            (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
          grouped entered.2.coord (mixedTable seed ro (.inl entered)) =
            literalRaw initial.1 a.native.wire.tape entered.2.coord := by
  obtain ⟨trace,answers,blocks⟩ := mixed_success_full_answers
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨initial,initialState,literals⟩ := trace_literals a.input.record.root
    (completion_chain registry.context Q a.input.packet) trace
  refine ⟨initial,initialState,?_⟩
  intro current member
  obtain ⟨raw,inHistory⟩ := answers current member
  obtain ⟨bounded,_⟩ := mixed_success_recorded cap registry Q attacker A B limit counted seed ro a success current member
  refine ⟨bounded,?_⟩
  have groupedEq := observed_grouped registry.context rfl Q B current bounded
    (completion_profiles registry.context Q a.input.packet current member)
    (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
    seed ro raw (blocks current raw inHistory)
  have literal := literals current raw inHistory
    (completion_profiles registry.context Q a.input.packet current member)
  have lifted := congrArg
    (Eq.mp (congrArg PCSBCSRounds.Raw (entered_query registry.context rfl Q B current bounded
      (completion_profiles registry.context Q a.input.packet current member)
      (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)))) literal
  have castEq := literal_cast initial.1 a.native.wire.tape _ _
    (entered_query registry.context rfl Q B current bounded
      (completion_profiles registry.context Q a.input.packet current member)
      (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member))
  exact groupedEq.trans (lifted.symm.trans castEq)

/-- Full chronological tape coverage at the observed cap, on the whole
allocation program. Neither Q ≤ B nor suffix-cache equality is required. -/
theorem mixed_success_tape (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∃ initial : RingPCSGame.Prefix × E,
      ∃ bounded : pathCost (RawWHIRKeys.coordinate registry.context a.input.packet.val 0) ≤ B,
        let packetB := PCSBCSNativePacketVisit.packetAtBound registry.context Q B a.input.packet bounded
        let final := PCSBCSNativePacketBridge.enteredPacket registry.context rfl B packetB
        a.native.wire.initial = some initial ∧
        a.input.packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config a.input.packet.val.profile) ∧
        final.2.coord = lastCoordinate (ParameterBounds.config a.input.packet.val.profile) ∧
        PCSBCSNativePacketBridge.completionPackets registry.context rfl B packetB =
          PCSBCSCapturedSourceStatePath.packets final ∧
        (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
          (⟨.inl current,mixedTable seed ro (.inl current)⟩ : Sigma PCSBCSSourceRootCapture.Answer) ∈
            (Sampling.execute (mixedTable seed ro)
              (allocationProgram (p := a.input.packet.val.profile)
                (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
                (wholeProgram cap registry Q attacker) A limit counted)).2) ∧
        (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
          grouped current.2.coord (mixedTable seed ro (.inl current)) =
            literalRaw initial.1 a.native.wire.tape current.2.coord) := by
  classical
  obtain ⟨initial,initialState,literals⟩ := mixed_success_literal_packets
    cap registry Q attacker A B limit counted seed ro a success
  have self : a.input.packet ∈ completion registry.context Q a.input.packet :=
    List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨bounded,_⟩ := mixed_success_recorded cap registry Q attacker A B limit counted seed ro a success a.input.packet self
  let packetB := PCSBCSNativePacketVisit.packetAtBound registry.context Q B a.input.packet bounded
  let final := PCSBCSNativePacketBridge.enteredPacket registry.context rfl B packetB
  have depth := mixed_success_depth cap registry Q attacker A B limit counted seed ro a success
  have ordering := PCSBCSNativePacketBridge.completionPackets_eq_of_length registry.context rfl B packetB depth
  have packetMember : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
      ∃ native, ∃ member : native ∈ completion registry.context Q a.input.packet,
        ∃ bound : pathCost (RawWHIRKeys.coordinate registry.context native.val 0) ≤ B,
          current = PCSBCSNativePacketBridge.enteredPacketAt registry.context rfl B
            (PCSBCSNativePacketVisit.packetAtBound registry.context Q B native bound)
            (completion_profiles registry.context Q a.input.packet native member)
            (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet native member) := by
    intro current member
    rw [← ordering] at member
    obtain ⟨attached,_,equal⟩ := List.mem_map.mp member
    have nativeMember : attached.val.val ∈ (completion registry.context Q a.input.packet).map Subtype.val := by
      rw [completion_data a.input.packet packetB rfl]
      exact List.mem_map.mpr ⟨attached.val,attached.property,rfl⟩
    obtain ⟨native,member,same⟩ := List.mem_map.mp nativeMember
    obtain ⟨bound,_⟩ := mixed_success_recorded cap registry Q attacker A B limit counted seed ro a success native member
    refine ⟨native,member,bound,?_⟩
    rw [← equal]
    apply entered_ext
    · rw [PCSBCSNativePacketBridge.enteredPacketAt_entry,PCSBCSNativePacketBridge.enteredPacketAt_entry]
      rfl
    · rw [PCSBCSNativePacketBridge.enteredPacketAt_messages,PCSBCSNativePacketBridge.enteredPacketAt_messages]
      exact congrArg RawWHIRKeys.PacketData.messages same.symm
  refine ⟨initial,bounded,initialState,depth,
    PCSBCSNativePacketBridge.query_eq_last_of_length registry.context B packetB depth,ordering,?_,?_⟩
  · intro current member
    obtain ⟨native,nativeMem,bound,equal⟩ := packetMember current member
    subst current
    obtain ⟨_,recorded⟩ := mixed_success_recorded cap registry Q attacker A B limit counted seed ro a success native nativeMem
    exact recorded
  · intro current member
    obtain ⟨native,nativeMem,bound,equal⟩ := packetMember current member
    subst current
    obtain ⟨_,raw⟩ := literals native nativeMem
    exact raw

/-- Actual caller preparation reads its genuine queried construction answers.
This statement is separate from address admission; no hidden coverage premise
is needed to decide the public address. -/
theorem mixed_success_caller_preparation (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∃ before,
      AnchoredPhysicalDriver.request .fresh cap a.input.packet.val.profile
        (registry.packetModel Q a.input.packet).layout a.input.record
        (RawWHIRKeys.entry registry.context a.input.packet.val)
        (WHIRPhysicalCaller.latestAnswers before) = some a.native.request ∧
      ∀ wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry registry.context a.input.packet.val),
        WHIRPhysicalCaller.latestAnswers before wanted =
          some (PCSBCSSourceCallerAnswers.answers
            (mixedTable (p := a.input.packet.val.profile) (iv := registry.context.iv)
              (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length) seed ro) wanted) := by
  obtain ⟨earlierTrace,after,split,_,run,_⟩ := mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨⟨before,physical,nativeSplit,_,queries,parsed⟩,_,_,_,_⟩ :=
    AnchoredPhysicalExecution.verifySource_execution cap .fresh (registry.packetModel Q a.input.packet)
      registry.context rfl Q a.input.packet a.input.record a.input.proofs after a.native run
  refine ⟨before,parsed,?_⟩
  intro wanted prior
  have queried : Query.construction wanted
      (RawWHIRKeys.callerOutput_admissible registry.context Q a.input.packet wanted prior) ∈
      before.map Observation.query := by
    rw [queries]
    exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨o,member,equal⟩ := List.mem_map.mp queried
  apply WHIRPhysicalCaller.latestAnswers_consistent before wanted
    (RawWHIRKeys.callerOutput_admissible registry.context Q a.input.packet wanted prior) _ ⟨o,member,equal⟩
  intro observation member valid same
  have present : observation ∈ (mixedView cap registry Q attacker A B limit counted seed ro).observations := by
    rw [split,nativeSplit]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  have construction : (⟨.construction wanted valid,observation.answer⟩ : Observation) ∈
      (mixedView cap registry Q attacker A B limit counted seed ro).observations := by
    cases observation
    cases same
    exact present
  simp only [mixedView,PublicCompressionCouplingMixed.compile_actual] at construction
  obtain ⟨bounded,actual⟩ := PCSBCSIdealConstructionAnswers.construction_observations
    (DuplexPublicSimulator.simulator B) ro registry.context.iv ⟨seed,[]⟩
    (wholeProgram cap registry Q attacker) A limit counted wanted valid _ construction
  rw [PCSBCSNativeIdealCallerOriginal.split_answers seed ro wanted bounded]
  exact actual

theorem mixed_success_fresh_decode (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∃ claims, AnchoredSourceFreshCaller.decode (registry.packetModel Q a.input.packet).layout
      a.input.record (RawWHIRKeys.entry registry.context a.input.packet.val)
      (PCSBCSSourceCallerAnswers.answers
        (mixedTable (p := a.input.packet.val.profile) (iv := registry.context.iv)
          (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length) seed ro)) = some claims := by
  obtain ⟨before,parsed,earlier⟩ := mixed_success_caller_preparation
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨claims,caller,_,_,_⟩ := AnchoredPhysicalDriver.request_origin .fresh cap a.input.packet.val.profile
    (registry.packetModel Q a.input.packet).layout a.input.record (RawWHIRKeys.entry registry.context a.input.packet.val)
    (WHIRPhysicalCaller.latestAnswers before) a.native.request parsed
  refine ⟨claims,?_⟩
  have tokens := WHIRCallerClaims.entryTokens_prior_only (RawWHIRKeys.entry registry.context a.input.packet.val)
    (fun q => (WHIRPhysicalCaller.latestAnswers before q).getD DuplexRefinement.zeroDigest)
    (PCSBCSSourceCallerAnswers.answers
      (mixedTable (p := a.input.packet.val.profile) (iv := registry.context.iv)
        (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length) seed ro))
    (by intro q member; rw [earlier q member]; rfl)
  simpa only [AnchoredPhysicalDriver.decodeCaller,AnchoredSourceFreshCaller.decode,tokens] using caller

theorem mixed_success_address_member (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a)
    (current : EnteredPacket a.input.packet.val.profile B registry.context.iv
      (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
    (entry : current.1.val = RawWHIRKeys.entry registry.context a.input.packet.val)
    (messages : current.2.messages = a.input.packet.val.messages) :
    ∀ opening ∈ a.native.wire.openings,
      PCSBCSCapturedIdealNativeAcceptance.openingReference registry.context Q a.input.packet opening
        a.input.record.shape.lanes ∈ PCSBCSCapturedSourceTransport.address (.inl current) := by
  obtain ⟨_,after,_,_,run,_⟩ := mixed_success_native_segment cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨valid,profile,roles,member⟩ := PCSBCSNativeRootRoles.verifySource_opening_member
    cap .fresh (registry.packetModel Q a.input.packet) registry.context rfl Q
    a.input.packet a.input.record a.input.proofs after a.native run
  obtain ⟨claims,caller⟩ := mixed_success_fresh_decode cap registry Q attacker A B limit counted seed ro a success
  have admitted := PCSBCSCapturedSourceTransport.address_packet (registry.packetModel Q a.input.packet).layout
    a.input.record _ current valid profile claims (by simpa only [entry] using caller)
    (by simpa only [messages] using roles)
  rw [admitted,messages]
  exact member

/-- Every retained actual opening has a genuine first-address prefix in the
whole execution, including any earlier attacker mention of the same root. -/
theorem mixed_success_opening_firstMention (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a) :
    ∀ opening ∈ a.native.wire.openings, ∃ events,
      PCSBCSFirstRootDisclosure.firstMention
        (PCSBCSCapturedSourceTransport.address (iv := registry.context.iv))
        (PCSBCSCapturedIdealNativeAcceptance.openingReference registry.context Q a.input.packet opening
          a.input.record.shape.lanes)
        (allocationProgram (p := a.input.packet.val.profile)
          (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
          (wholeProgram cap registry Q attacker) A limit counted)
        (mixedTable seed ro) = some events := by
  classical
  have self : a.input.packet ∈ completion registry.context Q a.input.packet :=
    List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨bounded,recorded⟩ := mixed_success_recorded cap registry Q attacker A B limit counted seed ro a success a.input.packet self
  let current := PCSBCSNativePacketBridge.enteredPacketAt registry.context rfl B
    (PCSBCSNativePacketVisit.packetAtBound registry.context Q B a.input.packet bounded)
    (completion_profiles registry.context Q a.input.packet a.input.packet self)
    (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet a.input.packet self)
  have entry : current.1.val = RawWHIRKeys.entry registry.context a.input.packet.val :=
    PCSBCSNativePacketBridge.enteredPacketAt_entry registry.context rfl B _ _ _
  have messages : current.2.messages = a.input.packet.val.messages :=
    PCSBCSNativePacketBridge.enteredPacketAt_messages registry.context rfl B _ _ _
  intro opening member
  apply PCSBCSFirstRootDisclosure.first_mention_exists _ (.inl current) _
    (mixed_success_address_member cap registry Q attacker A B limit counted seed ro a success current entry messages opening member)
  exact List.mem_map.mpr ⟨_,recorded,rfl⟩

end Whole

section Actual
variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)
    (attacker : Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (A B : Nat) (limit : A ≤ B) (counted : DuplexModeGame.Counts A (wholeProgram cap registry Q attacker))
    (C : PrimitiveOracle)

theorem actual_mixedView :
    mixedView cap registry Q attacker A B limit counted C (WHIRRealSimulator.rawTable B C) =
      (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view := by
  rw [mixedView,PublicCompressionCouplingMixed.compile_actual]
  exact WHIRRealSimulator.runIdeal_view C registry.context.iv _ ⟨rfl,by simp⟩ _ _ limit _

theorem actual_success_fullWidth_packets (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value = some a) :
    ∀ current (member : current ∈ completion registry.context Q a.input.packet),
      ∃ raw : GroupAnswer registry.context Q (.inl current),
        ∃ bounded : pathCost (RawWHIRKeys.coordinate registry.context current.val 0) ≤ B,
          let packetB := PCSBCSNativePacketVisit.packetAtBound registry.context Q B current bounded
          let entered := PCSBCSNativePacketBridge.enteredPacketAt registry.context rfl B packetB
            (completion_profiles registry.context Q a.input.packet current member)
            (PCSBCSNativePacketBridge.completion_entries registry.context Q a.input.packet current member)
          (⟨.inl current,raw⟩ : Sigma (GroupAnswer registry.context Q)) ∈ a.native.history ∧
          HEq (actualTable C (.inl entered))
            (PCSBCSNativePacketCodec.nativeFullBlocksEquiv registry.context rfl B packetB raw) ∧
          (⟨.inl entered,actualTable C (.inl entered)⟩ : Sigma PCSBCSSourceRootCapture.Answer) ∈
            (Sampling.execute (actualTable C)
              (allocationProgram (p := a.input.packet.val.profile)
                (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
                (wholeProgram cap registry Q attacker) A limit counted)).2 := by
  apply mixed_success_fullWidth_packets cap registry Q attacker A B limit counted C
    (WHIRRealSimulator.rawTable B C) a
  rwa [actual_mixedView cap registry Q attacker A B limit counted C]

theorem actual_success_tape (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value = some a) :
    ∃ initial : RingPCSGame.Prefix × E,
      ∃ bounded : pathCost (RawWHIRKeys.coordinate registry.context a.input.packet.val 0) ≤ B,
        let packetB := PCSBCSNativePacketVisit.packetAtBound registry.context Q B a.input.packet bounded
        let final := PCSBCSNativePacketBridge.enteredPacket registry.context rfl B packetB
        a.native.wire.initial = some initial ∧
        a.input.packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config a.input.packet.val.profile) ∧
        final.2.coord = lastCoordinate (ParameterBounds.config a.input.packet.val.profile) ∧
        PCSBCSNativePacketBridge.completionPackets registry.context rfl B packetB =
          PCSBCSCapturedSourceStatePath.packets final ∧
        (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
          (⟨.inl current,actualTable C (.inl current)⟩ : Sigma PCSBCSSourceRootCapture.Answer) ∈
            (Sampling.execute (actualTable C)
              (allocationProgram (p := a.input.packet.val.profile)
                (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
                (wholeProgram cap registry Q attacker) A limit counted)).2) ∧
        (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
          grouped current.2.coord (actualTable C (.inl current)) =
            literalRaw initial.1 a.native.wire.tape current.2.coord) := by
  apply mixed_success_tape cap registry Q attacker A B limit counted C (WHIRRealSimulator.rawTable B C) a
  rwa [actual_mixedView cap registry Q attacker A B limit counted C]

theorem actual_success_opening_firstMention (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value = some a) :
    ∀ opening ∈ a.native.wire.openings, ∃ events,
      PCSBCSFirstRootDisclosure.firstMention
        (PCSBCSCapturedSourceTransport.address (iv := registry.context.iv))
        (PCSBCSCapturedIdealNativeAcceptance.openingReference registry.context Q a.input.packet opening
          a.input.record.shape.lanes)
        (allocationProgram (p := a.input.packet.val.profile)
          (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
          (wholeProgram cap registry Q attacker) A limit counted)
        (actualTable C) = some events := by
  apply mixed_success_opening_firstMention cap registry Q attacker A B limit counted C
    (WHIRRealSimulator.rawTable B C) a
  rwa [actual_mixedView cap registry Q attacker A B limit counted C]

/-- Source counts and reachable native budgets suffice; no supplied root
admission or physical-freeze certificate is an endpoint premise. -/
theorem counted_whole_success_opening_firstMention
    (a b : Nat) (attackerCounted : WHIRSourceChronology.Counts a attacker)
    (budget : WHIRSourceBackfill.AllResults
      (fun input => sourceBudget registry.context Q input.packet ≤ b) (erase attacker))
    (limit : a+b ≤ B) (accepted : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value = some accepted) :
    ∀ opening ∈ accepted.native.wire.openings, ∃ events,
      PCSBCSFirstRootDisclosure.firstMention
        (PCSBCSCapturedSourceTransport.address (iv := registry.context.iv))
        (PCSBCSCapturedIdealNativeAcceptance.openingReference registry.context Q accepted.input.packet opening
          accepted.input.record.shape.lanes)
        (allocationProgram (p := accepted.input.packet.val.profile)
          (boundary := (RawWHIRKeys.entry registry.context accepted.input.packet.val).frames.length)
          (wholeProgram cap registry Q attacker) (a+b) limit
          (PCSBCSNativePhysicalFreeze.whole_counted cap registry Q attacker a b attackerCounted budget))
        (actualTable C) = some events :=
  actual_success_opening_firstMention cap registry Q attacker (a+b) B limit
    (PCSBCSNativePhysicalFreeze.whole_counted cap registry Q attacker a b attackerCounted budget)
    C accepted success

end Actual

#print axioms mixedView_runs
#print axioms mixed_success_native_segment
#print axioms mixed_success_recorded
#print axioms mixed_success_full_answers
#print axioms mixed_success_literal_packets
#print axioms mixed_success_tape
#print axioms mixed_success_caller_preparation
#print axioms mixed_success_fresh_decode
#print axioms mixed_success_address_member
#print axioms mixed_success_opening_firstMention
#print axioms fullWidth_of_answers
#print axioms mixed_success_fullWidth_packets
#print axioms actual_success_fullWidth_packets
#print axioms actual_success_tape
#print axioms actual_success_opening_firstMention
#print axioms counted_whole_success_opening_firstMention
end Whir.PCSBCSWholeNativePacketCoverage
