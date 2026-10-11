import Whir.WHIRRawReplay

/-! Canonical raw-cache provenance becomes the actual typed full-input history. -/
namespace Whir.WHIRRawHistory
open RawOracleCoupling RawOracleCoupling.Concrete WHIRRawReplay
open TypedOracleCompiler TypedFiatShamirGame
open RawWHIRKeys

variable (ctx : Context) (stack : ctx.mode = .stack) (Q : Nat)

abbrev Ancestors (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (packet : Packet ctx Q) :=
  dependencyHistory (dependencyKeys ctx Q) cache (.inl packet)

abbrev CallerHistory (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (packet : Packet ctx Q) :=
  (callerGroups ctx Q packet).filterMap
    (fun raw => (cache (.inr raw)).map (fun answer => (⟨.inr raw,answer⟩ : Sigma (GroupAnswer ctx Q))))

theorem ancestors_eq (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (packet : Packet ctx Q) :
    Ancestors ctx Q cache packet = CallerHistory ctx Q cache packet ++
      (RawWHIRKeys.ancestors ctx Q packet).filterMap
        (fun p => (cache (.inl p)).map (fun raw => (⟨.inl p,raw⟩ : Sigma (GroupAnswer ctx Q)))) := by
  simp only [Ancestors, dependencyHistory, dependencyKeys, Partition.dependencies,
    schedule, callerPlan, List.filterMap_append, List.filterMap_map]
  apply congrArg₂ List.append
  · exact List.filterMap_map
  · rfl

theorem decode_callers (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (calls : List (partition ctx Q).Garbage) :
    decodeHistory ctx stack Q (calls.filterMap
      (fun raw => (cache (.inr raw)).map (fun answer => (⟨.inr raw,answer⟩ : Sigma (GroupAnswer ctx Q))))) = [] := by
  induction calls with
  | nil => rfl
  | cons raw rest ih =>
    cases hit : cache (.inr raw) <;>
      simp [List.filterMap_cons, hit, decodeHistory, decodeEntry] at ih ⊢ <;> exact ih

/-- Caller values are privately available in the raw annotation, while their
garbage tags prevent them from changing the canonical typed WHIR ancestors. -/
theorem decoded_ancestors_eq (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (packet : Packet ctx Q) :
    decodeHistory ctx stack Q (Ancestors ctx Q cache packet) =
      decodeHistory ctx stack Q ((RawWHIRKeys.ancestors ctx Q packet).filterMap
        (fun p => (cache (.inl p)).map (fun raw => (⟨.inl p,raw⟩ : Sigma (GroupAnswer ctx Q))))) := by
  rw [ancestors_eq]
  have callers := decode_callers ctx stack Q cache (callerGroups ctx Q packet)
  simp only [decodeHistory, List.filterMap_append, List.reverse_append]
  change _ ++ decodeHistory ctx stack Q (CallerHistory ctx Q cache packet) = _
  rw [callers, List.append_nil]

 theorem ancestor_history_append (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (packet parent : Packet ctx Q) (raw : GroupAnswer ctx Q (.inl parent))
    (chain : RawWHIRKeys.ancestors ctx Q packet = RawWHIRKeys.ancestors ctx Q parent ++ [parent])
    (hit : cache (.inl parent) = some raw) :
    decodeHistory ctx stack Q (Ancestors ctx Q cache packet) =
      packetEntry ctx stack Q parent raw :: decodeHistory ctx stack Q (Ancestors ctx Q cache parent) := by
  rw [decoded_ancestors_eq, chain, List.filterMap_append, decoded_ancestors_eq]
  simp only [List.filterMap_cons, hit, Option.map_some, List.filterMap_nil]
  simp [decodeHistory, decodeEntry]

 theorem allocated_decoded (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (trace : List (Sigma (AllocationAnswer ctx Q)))
    (recorded : Recorded (dependencyKeys ctx Q) cache trace)
    (packet : Packet ctx Q) (raw : GroupAnswer ctx Q (.inl packet))
    (hit : cache (.inl packet) = some raw) :
    (⟨allocationKey ctx stack Q packet (Ancestors ctx Q cache packet),
      decodePacket ctx stack Q packet raw⟩ : Sigma GlobalAnswer) ∈ decodedTrace ctx stack Q trace := by
  apply List.mem_filterMap.mpr
  exact ⟨_, (recorded _ _ hit).2, rfl⟩


theorem cons_packet (packet : Packet ctx Q) (raw : GroupAnswer ctx Q (.inl packet))
    (past : List GlobalEntry) (trace : List (Sigma GlobalAnswer))
    (prior : HistoryRecorded globalQuery (packet.val.profile,RawWHIRKeys.entry ctx packet.val) trace
      packet.val.messages.tail past)
    (allocated : (⟨⟨(packet.val.profile,RawWHIRKeys.entry ctx packet.val),packet.val.messages,past⟩,
      decodePacket ctx stack Q packet raw⟩ : Sigma GlobalAnswer) ∈ trace) :
    HistoryRecorded globalQuery (packet.val.profile,RawWHIRKeys.entry ctx packet.val) trace
      packet.val.messages (packetEntry ctx stack Q packet raw :: past) := by
  rcases packet with ⟨⟨statement,profile,messages,entryFrames⟩,valid⟩
  cases messages with
  | nil => exact (valid.2.1 rfl).elim
  | cons m tail => exact .cons _ prior allocated

theorem recorded_history (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (trace : List (Sigma (AllocationAnswer ctx Q)))
    (recorded : Recorded (dependencyKeys ctx Q) cache trace)
    (packet : Packet ctx Q) (raw : GroupAnswer ctx Q (.inl packet))
    (hit : cache (.inl packet) = some raw) :
    HistoryRecorded globalQuery (packet.val.profile,RawWHIRKeys.entry ctx packet.val)
      (decodedTrace ctx stack Q trace) packet.val.messages
      (packetEntry ctx stack Q packet raw :: decodeHistory ctx stack Q (Ancestors ctx Q cache packet)) := by
  generalize hn : packet.val.messages.length = n
  induction n using Nat.strong_induction_on generalizing packet with
  | h n ih =>
    apply cons_packet ctx stack Q packet raw _ _
    · by_cases empty : packet.val.messages.drop 1 = []
      · have one : packet.val.messages.length = 1 := by
          have hp := List.length_pos_iff.mpr packet.property.2.1
          have h := congrArg List.length empty
          simp only [List.length_drop, List.length_nil] at h
          omega
        have ancestorsNil := ancestors_singleton ctx Q packet one
        have pastNil : decodeHistory ctx stack Q (Ancestors ctx Q cache packet) = [] := by
          rw [decoded_ancestors_eq, ancestorsNil]
          rfl
        have tailNil : packet.val.messages.tail = [] := by simpa only [List.drop_one] using empty
        simp only [pastNil, tailNil]
        exact .nil
      · let parent := dropPacket ctx Q packet 1 empty
        have chain : ancestors ctx Q packet = ancestors ctx Q parent ++ [parent] :=
          ancestors_drop_one ctx Q packet empty
        have parentMem : (.inl parent : GroupKey ctx Q) ∈
            dependencyKeys ctx Q (.inl packet) := by
          apply List.mem_append_right
          change Sum.inl parent ∈ (ancestors ctx Q packet).map Sum.inl
          rw [chain]
          simp
        obtain ⟨parentRaw,parentHit⟩ := (recorded _ _ hit).1 _ parentMem
        have shorter : parent.val.messages.length < n := by
          dsimp [parent,dropPacket]
          rw [List.length_drop]
          have hp := List.length_pos_iff.mpr packet.property.2.1
          omega
        have previous := ih parent.val.messages.length shorter parent parentRaw parentHit rfl
        rw [ancestor_history_append ctx stack Q cache packet parent parentRaw chain parentHit]
        simpa only [parent,dropPacket, RawWHIRKeys.entry, List.drop_one] using previous
    · exact allocated_decoded ctx stack Q cache trace recorded packet raw hit

/-- Actual final completion supplies both the cache entry and the fully decoded
canonical history theorem. No correctness/provenance certificate is an input. -/
theorem final_history {R : Type} {K : Nat} (final : R → Option (Packet ctx Q))
    (program : Sampling (DuplexModeGame.RawKey Q) (fun _ => FiatShamirGame.Digest32) R K)
    {trace result} (run : Sampling.Runs (RawOracleCoupling.Concrete.compile ctx Q final program) trace result)
    (packet : Packet ctx Q) (selected : final result.1 = some packet) :
    ∃ raw : GroupAnswer ctx Q (.inl packet),
      result.2 (.inl packet) = some raw ∧
      HistoryRecorded globalQuery (packet.val.profile,RawWHIRKeys.entry ctx packet.val)
        (decodedTrace ctx stack Q trace) packet.val.messages
        (packetEntry ctx stack Q packet raw ::
          decodeHistory ctx stack Q (Ancestors ctx Q result.2 packet)) := by
  have hr := RawOracleCoupling.Concrete.recorded ctx Q final program run
  obtain ⟨raw,hit⟩ := hr.1 packet
    (by simp [selected, terminalCompletion, completion])
  exact ⟨raw,hit,recorded_history ctx stack Q result.2 trace hr.2 packet raw hit⟩
end Whir.WHIRRawHistory
