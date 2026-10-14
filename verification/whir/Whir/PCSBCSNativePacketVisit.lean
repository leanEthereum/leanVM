import Whir.AnchoredPhysicalExecution
import Whir.PCSBCSMixedConstructionTrace
import Whir.PCSBCSNativePacketBridge
import Whir.PCSBCSCapturedIdealNativeAcceptance

/-! Native packet visitation is obtained from successful source execution,
not from an assumed complete allocation cache. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativePacketVisit
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRSourceChronology
open RawOracleCoupling.Concrete
open PublicMerkleProgram MerkleTransport MerkleTransport.Commitments

private theorem readPacket_first {n : Nat} (positive : 0 < n) (request : Fin n → Query)
    (raw : Fin n → Digest32) (observations : List Observation)
    (run : Runs (WHIRModeProgram.readPacket n request Program.done) observations raw) :
    ∃ answer, (⟨request ⟨0,positive⟩,answer⟩ : Observation) ∈ observations := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [WHIRModeProgram.readPacket] at run
    cases run with
    | ask answer rest => exact ⟨answer,List.mem_cons_self⟩

theorem readPhysicalPackets_queried {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (p : ParameterBounds.Profile) (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) (state : WireState p)
    (next : WireState p → List (Sigma (GroupAnswer ctx Q)) → Source cap (Option R))
    (observations : List Observation) (result : R)
    (run : Runs (erase (readPhysicalPackets ctx stack Q p lanes proofs none
      packets profiles state next)) observations (some result)) :
    ∀ packet ∈ packets, ∃ answer,
      (⟨WHIRModeFinal.request ctx Q packet ⟨0,RawWHIRKeys.blocks_positive ctx packet.val⟩,answer⟩ :
        Observation) ∈ observations := by
  induction packets generalizing state next observations with
  | nil => simp
  | cons packet packets ih =>
    simp only [readPhysicalPackets] at run
    cases parsed : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) with
    | none => simp only [parsed,erase] at run; cases run
    | some value =>
      obtain ⟨absorbed,root⟩ := value
      simp only [parsed] at run
      split at run
      · rw [announce_erase,sourceLift_erase] at run
        obtain ⟨before,nonce,after,whole,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases boundNonce : afterNonce absorbed nonce with
        | none => simp only [boundNonce,erase] at continued; cases continued
        | some bound =>
          simp only [boundNonce] at continued
          split at continued
          · rw [sourceLift_erase] at continued
            obtain ⟨beforeRaw,raw,afterRaw,rawWhole,readRaw,read⟩ := (Runs.bind_iff _ _).mp continued
            rw [sourceLift_erase] at read
            obtain ⟨beforeOpen,opened,afterOpen,openWhole,_,rest⟩ := (Runs.bind_iff _ _).mp read
            cases opened with
            | none => cases rest
            | some checked =>
              intro current member
              rcases List.mem_cons.mp member with same | later
              · subst current
                rw [readPacket_eq] at readRaw
                obtain ⟨answer,queried⟩ := readPacket_first
                  (RawWHIRKeys.blocks_positive ctx packet.val)
                  (WHIRModeFinal.request ctx Q packet) raw beforeRaw readRaw
                refine ⟨answer,?_⟩
                rw [whole,rawWhole]
                exact List.mem_append_right _ (List.mem_append_left _ queried)
              · obtain ⟨answer,queried⟩ := ih _ _ _ _ rest current later
                refine ⟨answer,?_⟩
                rw [whole,rawWhole,openWhole]
                exact List.mem_append_right _
                  (List.mem_append_right _ (List.mem_append_right _ queried))
          · cases continued
      · cases run

theorem verifySource_queried (cap : Nat) (boundary : AnchoredPhysicalDriver.Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (saved : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (accepted : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet saved proofs))
      observations (some accepted)) :
    ∀ current ∈ completion ctx Q packet, ∃ answer,
      (⟨WHIRModeFinal.request ctx Q current ⟨0,RawWHIRKeys.blocks_positive ctx current.val⟩,answer⟩ :
        Observation) ∈ observations := by
  obtain ⟨_,_,before,after,_,whole,_,_,_,physical⟩ :=
    AnchoredPhysicalExecution.verifySource_success cap boundary model ctx stack Q packet saved proofs
      observations accepted run
  intro current member
  obtain ⟨answer,queried⟩ := readPhysicalPackets_queried ctx stack Q packet.val.profile
    saved.shape.lanes proofs _ _ _ _ after accepted physical current member
  refine ⟨answer,?_⟩
  rw [whole]
  exact List.mem_append_right _ queried

/-- Reindex by the actual observed key's proved bound, not by an assumed
inequality between the native admission cap and aggregate source budget. -/
def packetAtBound (ctx : RawWHIRKeys.Context) (Q B : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B) :
    RawWHIRKeys.Packet ctx B :=
  ⟨packet.val,⟨packet.property.1,packet.property.2.1,packet.property.2.2.1,bounded,
    RawWHIRKeys.packet_entryValid ctx Q packet,RawWHIRKeys.packet_entryLength ctx Q packet,
    RawWHIRKeys.packet_callerOutputBound ctx Q packet⟩⟩

theorem packetAtBound_first_coordinate (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q B : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B)
    {p : ParameterBounds.Profile} {entry : FramedHistory}
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry) :
    let current := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
      (packetAtBound ctx Q B packet bounded) profile aligned
    current.2.2.coordinate current.2.firstBlock = RawWHIRKeys.coordinate ctx packet.val 0 := by
  cases profile
  cases aligned
  exact PCSBCSNativePacketBridge.sourcePacket_coordinate ctx stack B
    (packetAtBound ctx Q B packet bounded)
    (PCSBCSNativePacketBridge.canonicalPacket ctx stack B (packetAtBound ctx Q B packet bounded)).firstBlock

theorem observed_packet_recorded {R : Type} (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q B : Nat) (packet : RawWHIRKeys.Packet ctx Q) {p : ParameterBounds.Profile} {entry : FramedHistory}
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (program : Program R)
    (remaining : Nat) (limit : remaining ≤ B) (counted : DuplexModeGame.Counts remaining program)
    (answer : Digest32)
    (member : (⟨WHIRModeFinal.request ctx Q packet ⟨0,RawWHIRKeys.blocks_positive ctx packet.val⟩,answer⟩ :
      Observation) ∈ (runIdeal (DuplexPublicSimulator.simulator B) ro ctx.iv ⟨seed,log⟩
        program remaining limit counted).view.observations) :
    ∃ bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B,
      let current := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
        (packetAtBound ctx Q B packet bounded) profile aligned
      let part := PCSBCSChallengeOracle.EnteredPacket.partition
        (p := p) (Q := B) (iv := ctx.iv) (boundary := entry.frames.length)
      (⟨.inl current,(part.split (PublicCompressionCouplingMixed.oracle seed ro)) (.inl current)⟩ :
        Sigma (part.Answer (D := Digest32))) ∈
        (TypedOracleCompiler.Sampling.execute (part.split (PublicCompressionCouplingMixed.oracle seed ro))
          (PCSBCSChallengeOracle.Atomic.program part
            (PublicCompressionCouplingMixed.compile B ctx.iv log program remaining limit counted))).2 := by
  let coordinate := RawWHIRKeys.coordinate ctx packet.val 0
  have valid := RawWHIRKeys.coordinate_admissible ctx Q
    ⟨packet,⟨0,RawWHIRKeys.blocks_positive ctx packet.val⟩⟩
  obtain ⟨bounded,_⟩ := PCSBCSMixedConstructionTrace.ideal_recorded seed ro ctx.iv log
    program remaining limit counted coordinate valid answer member
  refine ⟨bounded,?_⟩
  let current := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
    (packetAtBound ctx Q B packet bounded) profile aligned
  let part := PCSBCSChallengeOracle.EnteredPacket.partition
    (p := p) (Q := B) (iv := ctx.iv) (boundary := entry.frames.length)
  apply PCSBCSMixedConstructionTrace.ideal_packet_recorded part seed ro ctx.iv log
    program remaining limit counted coordinate valid bounded answer ⟨current,current.2.firstBlock⟩ member
  have first := packetAtBound_first_coordinate ctx stack Q B packet bounded profile aligned
  have key : current.2.2.key current.2.firstBlock = constructionKey B ctx.iv coordinate bounded := by
    unfold PCSBCSChallengeOracle.SourcePacket.key
    congr 1
  rw [← key]
  exact PCSBCSChallengeOracle.EnteredPacket.recognize_block current current.2.firstBlock

theorem mixed_success_recorded (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat) (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (accepted : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet
      saved proofs ctx.iv B limit seed ro).result.value = some accepted) :
    ∀ current (member : current ∈ completion ctx Q packet),
      ∃ bounded : pathCost (RawWHIRKeys.coordinate ctx current.val 0) ≤ B,
        let entered := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
          (packetAtBound ctx Q B current bounded)
          (completion_profiles ctx Q packet current member)
          (PCSBCSNativePacketBridge.completion_entries ctx Q packet current member)
        (⟨.inl entered,(PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro) (.inl entered)⟩ :
          Sigma (PCSBCSSourceRootCapture.Answer)) ∈
          (TypedOracleCompiler.Sampling.execute
            (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)
            (PCSBCSCapturedIdealNativeAcceptance.allocationProgram
              cap model ctx stack Q packet saved proofs B limit)).2 := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  intro current member
  obtain ⟨answer,queried⟩ := verifySource_queried cap .fresh model ctx stack Q packet saved proofs
    _ accepted run current member
  have inIdeal : (⟨WHIRModeFinal.request ctx Q current
      ⟨0,RawWHIRKeys.blocks_positive ctx current.val⟩,answer⟩ : Observation) ∈
      (runIdeal (DuplexPublicSimulator.simulator B) ro ctx.iv ⟨seed,[]⟩
        (WHIRSourceChronology.compile
          (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
        (sourceBudget ctx Q packet) limit
        ((WHIRSourceChronology.compile_counted _ _).mpr
          (AnchoredPhysicalDriver.verifySource_counted cap .fresh model ctx stack Q packet saved proofs))).view.observations := by
    simpa only [AnchoredMixedIdealSourceAcceptance.mixedView,PublicCompressionCouplingMixed.compile_actual]
      using queried
  exact observed_packet_recorded ctx stack Q B current
    (completion_profiles ctx Q packet current member)
    (PCSBCSNativePacketBridge.completion_entries ctx Q packet current member) seed ro []
    (WHIRSourceChronology.compile
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
    (sourceBudget ctx Q packet) limit
    ((WHIRSourceChronology.compile_counted _ _).mpr
      (AnchoredPhysicalDriver.verifySource_counted cap .fresh model ctx stack Q packet saved proofs))
    answer inIdeal

#print axioms readPhysicalPackets_queried
#print axioms verifySource_queried
#print axioms packetAtBound_first_coordinate
#print axioms observed_packet_recorded
#print axioms mixed_success_recorded
end Whir.PCSBCSNativePacketVisit
