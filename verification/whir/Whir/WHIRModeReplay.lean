import Whir.WHIRCausalRawROM
import Whir.WHIRModeFinal

namespace Whir.WHIRModeReplay
open FiatShamirGame (Digest32)
open RawOracleCoupling RawOracleCoupling.Concrete WHIRRawReplay
open Classical
set_option maxHeartbeats 800000

/-- Only bytes actually returned by the metered final program are decoded. -/
def history (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (physical : List (Sigma (GroupAnswer ctx Q))) :=
  (decodeHistory ctx stack Q physical).filterMap (restrictEntry packet.val.profile)

theorem decode_completion (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (table : DuplexModeGame.RawKey Q → Digest32) (packet : RawWHIRKeys.Packet ctx Q) :
    decodeHistory ctx stack Q (WHIRModeFinal.idealCompletion ctx Q table (some packet)) =
      packetEntry ctx stack Q packet (WHIRModeFinal.idealPacket ctx Q table packet) ::
        decodeHistory ctx stack Q (WHIRModeFinal.idealHistory ctx Q table
          (RawWHIRKeys.ancestors ctx Q packet)) := by
  rw [WHIRModeFinal.idealCompletion_some]
  have callers : ((RawWHIRKeys.callerGroups ctx Q packet).map
      (fun key => (⟨.inr key,table key.val⟩ : Sigma (GroupAnswer ctx Q)))).filterMap
      (decodeEntry ctx stack Q) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro value member
    obtain ⟨key,_,equal⟩ := List.mem_map.mp member
    subst value
    rfl
  simp only [decodeHistory,List.filterMap_append]
  have dropped := congrArg (fun values : List GlobalEntry =>
    (values ++ (WHIRModeFinal.idealHistory ctx Q table
      (RawWHIRKeys.ancestors ctx Q packet ++ [packet])).filterMap (decodeEntry ctx stack Q)).reverse) callers
  apply dropped.trans
  simp only [WHIRModeFinal.idealHistory,List.map_append,List.map_cons,List.map_nil,
    List.filterMap_append,List.filterMap_cons,decodeEntry,
    List.filterMap_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.singleton_append]

private theorem cached_packets (ctx : RawWHIRKeys.Context) (Q : Nat)
    (table : DuplexModeGame.RawKey Q → Digest32)
    (cache : TypedFiatShamirGame.Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (packets : List (RawWHIRKeys.Packet ctx Q))
    (hits : ∀ packet ∈ packets, cache (.inl packet) =
      some (WHIRModeFinal.idealPacket ctx Q table packet)) :
    packets.filterMap (fun packet => (cache (.inl packet)).map
      (fun raw => (⟨.inl packet,raw⟩ : Sigma (GroupAnswer ctx Q)))) =
        WHIRModeFinal.idealHistory ctx Q table packets := by
  induction packets with
  | nil => rfl
  | cons packet rest ih =>
    have head := hits packet (by simp)
    have tail := ih (fun p h => hits p (List.mem_cons_of_mem packet h))
    simp only [List.filterMap_cons,head,Option.map_some,tail,
      WHIRModeFinal.idealHistory,List.map_cons]

theorem completed_history (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    (table : DuplexModeGame.RawKey Q → Digest32) (packet : RawWHIRKeys.Packet ctx Q)
    (selected : select (tableExecution ctx Q select program table).1 = some packet)
    (raw : GroupAnswer ctx Q (.inl packet))
    (hit : (tableExecution ctx Q select program table).2 (.inl packet) = some raw) :
    history ctx stack Q packet (WHIRModeFinal.idealCompletion ctx Q table (some packet)) =
      WHIRRawROM.completedHistory ctx stack Q (tableExecution ctx Q select program table).2 packet raw := by
  have cached := tableExecution_cached ctx Q select program table
  rw [selected] at cached
  have packetHits : ∀ p ∈ RawWHIRKeys.ancestors ctx Q packet,
      (tableExecution ctx Q select program table).2 (.inl p) =
        some (WHIRModeFinal.idealPacket ctx Q table p) := by
    intro p member
    obtain ⟨answer,found⟩ := cached p (List.mem_append_left [packet] member)
    have equal : WHIRModeFinal.idealPacket ctx Q table p = answer :=
      tableExecution_cache ctx Q select program table (.inl p) answer found
    exact found.trans (congrArg some equal.symm)
  have current : WHIRModeFinal.idealPacket ctx Q table packet = raw :=
    tableExecution_cache ctx Q select program table (.inl packet) raw hit
  unfold history WHIRRawROM.completedHistory
  rw [decode_completion,current,WHIRRawHistory.decoded_ancestors_eq,
    cached_packets ctx Q table _ _ packetHits]

/-- The verifier consumes only the explicit completed transcript, not an
ambient oracle. Catalog and root snapshots are separate caller bookkeeping. -/
def Failure (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : WHIRRawROM.Catalogs cap) (roots : WHIRRawROM.RootFamilies)
    (selected : Option (RawWHIRKeys.Packet ctx Q)) (physical : List (Sigma (GroupAnswer ctx Q))) : Prop :=
  ∃ packet, selected = some packet ∧
    StackWHIRROM.HistoryFailure packet.val.profile cap
      (WHIRRawROM.localCatalog catalog packet.val.profile (callerEntry ctx Q packet))
      (roots packet.val.profile) packet.val.statement packet.val.messages
      (history ctx stack Q packet physical)

theorem failure_iff_cache (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : WHIRRawROM.Catalogs cap) (roots : WHIRRawROM.RootFamilies)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    (table : DuplexModeGame.RawKey Q → Digest32) :
    Failure ctx stack Q cap catalog roots (select (tableExecution ctx Q select program table).1)
      (WHIRModeFinal.idealCompletion ctx Q table
        (select (tableExecution ctx Q select program table).1)) ↔
    WHIRRawROM.Failure ctx stack Q cap catalog roots
      (select (tableExecution ctx Q select program table).1)
      (tableExecution ctx Q select program table).2 := by
  constructor
  · rintro ⟨packet,selected,failed⟩
    have cached := tableExecution_cached ctx Q select program table
    rw [selected] at cached
    obtain ⟨raw,hit⟩ := cached packet (List.mem_append_right _ (by simp))
    refine ⟨packet,selected,raw,hit,?_⟩
    rw [selected,completed_history ctx stack Q select program table packet selected raw hit] at failed
    exact failed
  · rintro ⟨packet,selected,raw,hit,failed⟩
    refine ⟨packet,selected,?_⟩
    rw [selected,completed_history ctx stack Q select program table packet selected raw hit]
    exact failed

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _

/-- Exact raw-ROM bound for the explicit completed transcript. The binding
state here remains the causal interpreter's private state; this theorem does
not assert that it is reconstructible from a mode observer's public view. -/
theorem physical_table_list_binding (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : WHIRCausalRawROM.Resolver ctx Q cap)
    (initial : CausalBindingState.State cap) {R : Type} {K : Nat}
    (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K) :
    FiatShamirGame.average (fun table : DuplexModeGame.RawKey Q → Digest32 =>
      let result := tableExecution ctx Q select program table
      let final := WHIRCausalRawROM.stateOfResult ctx stack Q cap resolver initial select program result
      if Failure ctx stack Q cap final.catalog (CausalBindingState.roots final)
        (select result.1) (WHIRModeFinal.idealCompletion ctx Q table (select result.1))
        then 1 else 0) ≤
      min 1 (((allocationBudget ctx * (K+1) : Nat) : ℚ) * WHIRRawROM.epsilon cap) := by
  apply le_trans _ (WHIRCausalRawROM.raw_table_list_binding ctx stack Q cap resolver initial select program)
  apply le_of_eq
  apply congrArg FiatShamirGame.average
  funext table
  dsimp only
  rw [failure_iff_cache]

end Whir.WHIRModeReplay
