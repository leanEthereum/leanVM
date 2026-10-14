import Whir.WHIRPhysicalReplay
import Whir.PCSBCSCapturedSourceStatePath

/-! Deterministic stack packet conversion. The native packet supplies admission,
caller framing and the path cap. No source-execution or acceptance certificate is
part of this interface. Completion alignment below is scoped to a terminal
native packet; a partial reader is not asserted to finish the schedule. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSNativePacketBridge
open FiatShamirGame DuplexModeGame DuplexFraming CausalProbability
open PCSBCSChallengeOracle PCSBCSRounds WHIRHistory

variable (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)

def query (packet : RawWHIRKeys.Packet ctx Q) :=
  WHIRPhysicalVerifier.packetQuery ctx Q packet.val.profile packet rfl

def sourcePacket (packet : RawWHIRKeys.Packet ctx Q) :
    SourcePacket packet.val.profile Q ctx.iv (RawWHIRKeys.entry ctx packet.val)
      (query ctx Q packet) where
  messages := packet.val.messages
  nonempty := packet.property.2.1
  admitted := packet.property.2.2.1
  entryValid := RawWHIRKeys.packet_entryValid ctx Q packet
  position_eq := (WHIRPhysicalReplay.packetQuery_position ctx Q _ packet rfl).symm
  pathBound := by
    intro block
    have normal := WHIRHistoryKey.scheduled_normal _ _ packet.property.2.1 packet.property.2.2.1
    have bound := RawWHIRKeys.packet_pathBound ctx Q packet
    rw [← RawWHIRKeys.pathCost_block ctx packet.val block.val] at bound
    rw [RawWHIRKeys.coordinate_eq_outputKeyFrom ctx packet.val block.val normal] at bound
    simpa only [RawWHIRKeys.width, stack] using bound

def canonicalPacket (packet : RawWHIRKeys.Packet ctx Q) :
    CanonicalPacket packet.val.profile Q ctx.iv (RawWHIRKeys.entry ctx packet.val) :=
  ⟨query ctx Q packet, sourcePacket ctx stack Q packet⟩

def enteredPacket (packet : RawWHIRKeys.Packet ctx Q) :
    EnteredPacket packet.val.profile Q ctx.iv (RawWHIRKeys.entry ctx packet.val).frames.length :=
  ⟨⟨RawWHIRKeys.entry ctx packet.val, rfl⟩, canonicalPacket ctx stack Q packet⟩

/-- A common aggregate compiler cap is an explicit monotone reindex, not an
identification of the local packet cap with the verifier's aggregate cost. -/
def reindex {Q' : Nat} (bounded : Q ≤ Q') (packet : RawWHIRKeys.Packet ctx Q) :
    RawWHIRKeys.Packet ctx Q' :=
  ⟨packet.val, ⟨packet.property.1, packet.property.2.1, packet.property.2.2.1,
    (RawWHIRKeys.packet_pathBound ctx Q packet).trans bounded,
    RawWHIRKeys.packet_entryValid ctx Q packet, RawWHIRKeys.packet_entryLength ctx Q packet,
    RawWHIRKeys.packet_callerOutputBound ctx Q packet⟩⟩

@[simp] theorem reindex_coordinate {Q' : Nat} (bounded : Q ≤ Q')
    (packet : RawWHIRKeys.Packet ctx Q) (block : Nat) :
    RawWHIRKeys.coordinate ctx (reindex ctx Q bounded packet).val block =
      RawWHIRKeys.coordinate ctx packet.val block := rfl
/-- Both the reader's aggregate cost and the original packet path cap fit
here. In particular this does not assert `Q = sourceBudget`. -/
def commonCap (packet : RawWHIRKeys.Packet ctx Q) : Nat :=
  max Q (WHIRPhysicalVerifier.sourceBudget ctx Q packet)

def commonCapPacket (packet : RawWHIRKeys.Packet ctx Q) :
    RawWHIRKeys.Packet ctx (commonCap ctx Q packet) :=
  reindex ctx Q (Nat.le_max_left _ _) packet

theorem sourceBudget_le_commonCap (packet : RawWHIRKeys.Packet ctx Q) :
    WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ commonCap ctx Q packet :=
  Nat.le_max_right _ _

theorem reindex_dropPacket {Q' : Nat} (bounded : Q ≤ Q')
    (packet : RawWHIRKeys.Packet ctx Q) (n : Nat)
    (nonempty : packet.val.messages.drop n ≠ []) :
    reindex ctx Q bounded (RawWHIRKeys.dropPacket ctx Q packet n nonempty) =
      RawWHIRKeys.dropPacket ctx Q' (reindex ctx Q bounded packet) n nonempty :=
  Subtype.ext rfl
theorem reindex_ancestors {Q' : Nat} (bounded : Q ≤ Q')
    (packet : RawWHIRKeys.Packet ctx Q) :
    RawWHIRKeys.ancestors ctx Q' (reindex ctx Q bounded packet) =
      (RawWHIRKeys.ancestors ctx Q packet).map (reindex ctx Q bounded) := by
  unfold RawWHIRKeys.ancestors
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact (reindex_dropPacket ctx Q bounded packet _ _).symm

theorem reindex_completion {Q' : Nat} (bounded : Q ≤ Q')
    (packet : RawWHIRKeys.Packet ctx Q) :
    RawOracleCoupling.Concrete.completion ctx Q' (reindex ctx Q bounded packet) =
      (RawOracleCoupling.Concrete.completion ctx Q packet).map (reindex ctx Q bounded) := by
  simp only [RawOracleCoupling.Concrete.completion, List.map_append, List.map_singleton,
    reindex_ancestors]

theorem encode_reindex_expanded {Q' : Nat} (bounded : Q ≤ Q')
    (packet : RawWHIRKeys.Packet ctx Q) (b : Fin (RawWHIRKeys.blocks ctx packet.val)) :
    expandKey (RawWHIRKeys.encode ctx Q' ⟨reindex ctx Q bounded packet,b⟩) =
      expandKey (RawWHIRKeys.encode ctx Q ⟨packet,b⟩) := by
  unfold RawWHIRKeys.encode
  simp only [expand_constructionKey, reindex_coordinate]



/-- The drop is exactly the canonical predecessor at the same cap and literal
entry, including the domain, statement and all entry frames. -/
theorem dropPacket_eq_predecessor (packet : RawWHIRKeys.Packet ctx Q)
    (r : (canonicalPacket ctx stack Q packet).Earlier) :
    canonicalPacket ctx stack Q (RawWHIRKeys.dropPacket ctx Q packet
      (position (query ctx Q packet) - position r.val)
      ((canonicalPacket ctx stack Q packet).prefixMessages_nonempty r)) =
      (canonicalPacket ctx stack Q packet).predecessor r := by
  apply CanonicalPacket.messages_injective
  rfl

/-- Every conversion keeps the literal native entry, not merely its digest. -/
@[simp] theorem enteredPacket_entry (packet : RawWHIRKeys.Packet ctx Q) :
    (enteredPacket ctx stack Q packet).1.val = RawWHIRKeys.entry ctx packet.val := rfl

/-- Aligning proof indices changes no packet data. -/
def enteredPacketAt {p : ParameterBounds.Profile} {entry : FramedHistory}
    (packet : RawWHIRKeys.Packet ctx Q)
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry) :
    EnteredPacket p Q ctx.iv entry.frames.length := by
  cases profile
  cases aligned
  exact enteredPacket ctx stack Q packet

@[simp] theorem enteredPacketAt_messages {p : ParameterBounds.Profile} {entry : FramedHistory}
    (packet : RawWHIRKeys.Packet ctx Q)
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry) :
    (enteredPacketAt ctx stack Q packet profile aligned).2.messages = packet.val.messages := by
  cases profile
  cases aligned
  rfl

@[simp] theorem enteredPacketAt_entry {p : ParameterBounds.Profile} {entry : FramedHistory}
    (packet : RawWHIRKeys.Packet ctx Q)
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry) :
    (enteredPacketAt ctx stack Q packet profile aligned).1.val = entry := by
  cases profile
  cases aligned
  rfl

theorem completion_entries (packet : RawWHIRKeys.Packet ctx Q) :
    ∀ a ∈ RawOracleCoupling.Concrete.completion ctx Q packet,
      RawWHIRKeys.entry ctx a.val = RawWHIRKeys.entry ctx packet.val := by
  intro a member
  simp only [RawOracleCoupling.Concrete.completion, List.mem_append, List.mem_singleton] at member
  rcases member with prior | same
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp prior
    rfl
  · subst a
    rfl

def completionPackets (packet : RawWHIRKeys.Packet ctx Q) :
    List (EnteredPacket packet.val.profile Q ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length) :=
  (RawOracleCoupling.Concrete.completion ctx Q packet).attach.map fun a =>
    enteredPacketAt ctx stack Q a.val
      (WHIRPhysicalVerifier.completion_profiles ctx Q packet a.val a.property)
      (completion_entries ctx Q packet a.val a.property)

private theorem entered_ext {p : ParameterBounds.Profile} {entry : FramedHistory}
    (a b : EnteredPacket p Q ctx.iv entry.frames.length)
    (ae : a.1.val = entry) (be : b.1.val = entry)
    (messages : a.2.messages = b.2.messages) : a = b := by
  have same : a.1 = b.1 := Subtype.ext (ae.trans be.symm)
  cases a with
  | mk ea pa =>
    cases b with
    | mk eb pb =>
      cases same
      have eq := CanonicalPacket.messages_injective messages
      cases eq
      rfl

/-- Actual terminal position suffices for exact canonical completion. The
native list is not replaced by an assumed StatePath or a supplied packet list. -/
theorem completionPackets_eq (packet : RawWHIRKeys.Packet ctx Q)
    (terminal : query ctx Q packet =
      PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config packet.val.profile)) :
    completionPackets ctx stack Q packet =
      PCSBCSCapturedSourceStatePath.packets (enteredPacket ctx stack Q packet) := by
  have slot := WHIRPhysicalReplay.packetQuery_position ctx Q _ packet rfl
  change position (query ctx Q packet) = packet.val.messages.length-1 at slot
  rw [terminal, PCSBCSCapturedSourceStatePath.lastCoordinate_position] at slot
  have nonempty := List.length_pos_iff.mpr packet.property.2.1
  have depthPositive := WHIRHistory.position_lt_depth
    (.initial : Coordinate (ParameterBounds.config packet.val.profile))
  have length : packet.val.messages.length = depth (ParameterBounds.config packet.val.profile) := by omega
  apply List.ext_getElem
  · simp only [completionPackets, List.length_map, List.length_attach,
      RawOracleCoupling.Concrete.completion, List.length_append, List.length_singleton,
      RawWHIRKeys.ancestors_length, PCSBCSCapturedSourceStatePath.packets, List.length_map]
    change packet.val.messages.length-1+1 = depth _
    omega
  · intro i hi hj
    simp only [PCSBCSCapturedSourceStatePath.packets, List.length_map] at hj
    simp only [completionPackets, PCSBCSCapturedSourceStatePath.packets,
      List.getElem_map, List.getElem_attach]
    apply entered_ext ctx Q (entry := RawWHIRKeys.entry ctx packet.val)
    · exact enteredPacketAt_entry ctx stack Q _ _ _
    · exact congrArg Subtype.val (PCSBCSCapturedSourceStatePath.packetAt_entry _ _)
    · rw [enteredPacketAt_messages]
      have hpos := WHIRHistory.position_schedule_get
        (ParameterBounds.config packet.val.profile) ⟨i,hj⟩
      change position ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) = i at hpos
      have hjdepth : i < depth (ParameterBounds.config packet.val.profile) := hj
      rw [← length] at hjdepth
      have nativeLength : (RawWHIRKeys.ancestors ctx Q packet).length = packet.val.messages.length-1 :=
        RawWHIRKeys.ancestors_length ctx Q packet
      by_cases earlier : i < packet.val.messages.length-1
      · have before : position ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) <
          position (enteredPacket ctx stack Q packet).2.coord := by
          change position ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) <
            position (query ctx Q packet)
          rw [hpos]
          have pos := WHIRPhysicalReplay.packetQuery_position ctx Q _ packet rfl
          exact pos.symm ▸ earlier
        have eq : PCSBCSCapturedSourceStatePath.packetAt (enteredPacket ctx stack Q packet)
            ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) =
            (enteredPacket ctx stack Q packet).predecessor
              ⟨(schedule (ParameterBounds.config packet.val.profile))[i]'hj,before⟩ :=
          dite_eq_left before
        rw [eq]
        change ((RawWHIRKeys.ancestors ctx Q packet ++ [packet])[i]'_).val.messages =
          packet.val.messages.drop (position (query ctx Q packet) -
            position ((schedule (ParameterBounds.config packet.val.profile))[i]'hj))
        rw [hpos]
        have pos : position (query ctx Q packet) = packet.val.messages.length-1 :=
          WHIRPhysicalReplay.packetQuery_position ctx Q _ packet rfl
        rw [pos]
        rw [List.getElem_append_left (by omega)]
        exact (RawWHIRKeys.ancestors_get ctx Q packet ⟨i,earlier⟩).2
      · have notBefore : ¬ position ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) <
          position (enteredPacket ctx stack Q packet).2.coord := by
          change ¬ position ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) <
            position (query ctx Q packet)
          rw [hpos]
          have pos := WHIRPhysicalReplay.packetQuery_position ctx Q _ packet rfl
          exact pos.symm ▸ earlier
        have eq : PCSBCSCapturedSourceStatePath.packetAt (enteredPacket ctx stack Q packet)
            ((schedule (ParameterBounds.config packet.val.profile))[i]'hj) =
            enteredPacket ctx stack Q packet := dite_eq_right notBefore
        rw [eq]
        have atLast : i = (RawWHIRKeys.ancestors ctx Q packet).length := by
          omega
        change ((RawWHIRKeys.ancestors ctx Q packet ++ [packet])[i]'_).val.messages = packet.val.messages
        rw [List.getElem_append_right (by omega)]
        simp only [atLast, Nat.sub_self, List.getElem_cons_zero]

theorem sourcePacket_coordinate (packet : RawWHIRKeys.Packet ctx Q)
    (b : Fin (blocks (rawWidth (query ctx Q packet)))) :
    (sourcePacket ctx stack Q packet).coordinate b =
      RawWHIRKeys.coordinate ctx packet.val b.val := by
  have normal := WHIRHistoryKey.scheduled_normal _ _ packet.property.2.1 packet.property.2.2.1
  rw [RawWHIRKeys.coordinate_eq_outputKeyFrom ctx packet.val b.val normal]
  simp only [SourcePacket.coordinate, RawWHIRKeys.width, stack]
  rfl

theorem dropPacket_eq_enteredPredecessor (packet : RawWHIRKeys.Packet ctx Q)
    (r : (enteredPacket ctx stack Q packet).Earlier) :
    enteredPacket ctx stack Q (RawWHIRKeys.dropPacket ctx Q packet
      (position (query ctx Q packet) - position r.val)
      ((canonicalPacket ctx stack Q packet).prefixMessages_nonempty r)) =
      (enteredPacket ctx stack Q packet).predecessor r := by
  apply entered_ext ctx Q (entry := RawWHIRKeys.entry ctx packet.val)
  · rfl
  · rfl
  · rfl

/-- Terminality is derived from the native Pending length, so execution
inversion can use its completed depth without assuming a semantic StatePath. -/
theorem query_eq_last_of_length (packet : RawWHIRKeys.Packet ctx Q)
    (completed : packet.val.messages.length = depth (ParameterBounds.config packet.val.profile)) :
    query ctx Q packet = PCSRoundByRoundTranscriptState.lastCoordinate
      (ParameterBounds.config packet.val.profile) := by
  apply CausalPrefix.position_injective
  have pos : position (query ctx Q packet) = packet.val.messages.length-1 :=
    WHIRPhysicalReplay.packetQuery_position ctx Q _ packet rfl
  rw [pos, completed, PCSBCSCapturedSourceStatePath.lastCoordinate_position]

theorem completionPackets_eq_of_length (packet : RawWHIRKeys.Packet ctx Q)
    (completed : packet.val.messages.length = depth (ParameterBounds.config packet.val.profile)) :
    completionPackets ctx stack Q packet =
      PCSBCSCapturedSourceStatePath.packets (enteredPacket ctx stack Q packet) :=
  completionPackets_eq ctx stack Q packet (query_eq_last_of_length ctx Q packet completed)

include stack in
theorem packet_blocks_pcs (packet : RawWHIRKeys.Packet ctx Q) :
    RawWHIRKeys.blocks ctx packet.val = blocks (rawWidth (query ctx Q packet)) := by
  change (RawWHIRKeys.width ctx.mode packet.val.profile (packet.val.messages.length-1)+31)/32 = _
  simp only [RawWHIRKeys.width, stack]
  have width := (sourcePacket ctx stack Q packet).width_eq
  change WHIRHistoryKey.stackWidth (ParameterBounds.config packet.val.profile)
    (packet.val.messages.length-1) = 24*rawWidth (query ctx Q packet) at width
  rw [width]
  rfl

/-- Native partition and source packet addresses name the very same raw key. -/
theorem sourcePacket_key (packet : RawWHIRKeys.Packet ctx Q)
    (b : Fin (blocks (rawWidth (query ctx Q packet)))) :
    (sourcePacket ctx stack Q packet).key b =
      RawWHIRKeys.encode ctx Q ⟨packet,⟨b.val, by
        rw [packet_blocks_pcs ctx stack Q packet]
        exact b.isLt⟩⟩ := by
  unfold SourcePacket.key RawWHIRKeys.encode
  congr 1
  exact sourcePacket_coordinate ctx stack Q packet b

#print axioms sourcePacket_key
#print axioms completionPackets_eq_of_length


#print axioms completionPackets_eq
#print axioms sourcePacket
#print axioms dropPacket_eq_predecessor
end Whir.PCSBCSNativePacketBridge
