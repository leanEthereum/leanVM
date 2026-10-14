import Whir.AnchoredSourceRegistry
import Whir.AnchoredByteStreamPrepared
import Whir.WHIRSourceRawCache

/-! Actual raw-byte grouping is selected by the source header decoder. Preparation reuses the existing partial native-source replay and immutable first Merkle registry. It receives only completed raw history before the current group answer, including when the adversary first requests a nonzero point block. The simulator seed and total source resource certificate remain the explicit mode-game inputs. -/
namespace Whir.AnchoredSourceGroups
open Concrete FiatShamirGame DuplexModeGame ParameterBounds
open AnchoredHeaderRoots AnchoredByteStreamGroups
open WHIRSourceChronology

def accept (registry : Public) (p : Profile) (history : FramedHistory) : Bool :=
  (fromHistory registry history).any (fun header =>
    decide (header.shape.logN = (config p).logN ∧ header.shape.logBatch = (config p).folds[0]!))

abbrev Packet (registry : Public) (p : Profile) (Q : Nat) :=
  AnchoredByteStreamPrepared.PointPacket p Q registry.iv (accept registry p)

theorem packet_header (registry : Public) (p : Profile) (Q : Nat) (packet : Packet registry p Q) :
    ∃ header, fromHistory registry packet.val.history = some header ∧
      header.shape.logN = (config p).logN ∧ header.shape.logBatch = (config p).folds[0]! := by
  have valid := packet.property
  cases parsed : fromHistory registry packet.val.history with
  | none => simp [accept,parsed] at valid
  | some header =>
    have geometry : header.shape.logN = (config p).logN ∧ header.shape.logBatch = (config p).folds[0]! := by
      simpa [accept,parsed] using valid
    exact ⟨header,rfl,geometry⟩

noncomputable def header (registry : Public) (p : Profile) (Q : Nat) (packet : Packet registry p Q) : Header :=
  (packet_header registry p Q packet).choose

theorem header_parsed (registry : Public) (p : Profile) (Q : Nat) (packet : Packet registry p Q) :
    fromHistory registry packet.val.history = some (header registry p Q packet) :=
  (packet_header registry p Q packet).choose_spec.1

theorem header_batch (registry : Public) (p : Profile) (Q : Nat) (packet : Packet registry p Q) :
    (header registry p Q packet).shape.logBatch = (config p).folds[0]! :=
  (packet_header registry p Q packet).choose_spec.2.2

def rawState (cap Q : Nat) (past : ByteHistory Q) : CausalBindingState.State cap :=
  { rawAnswers := fun n => if equal : n = Q then equal.symm ▸ past else [] }

/-- The same source event replay used by the historical physical chain, now fed all counted original-CV/metadata/frame inputs from the new source. No asserted record table or future raw answer is accepted. -/
def updatePrefix (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) (past : ByteHistory Q)
    (state : AnchoredSourceRegistry.State cap) : AnchoredSourceRegistry.State cap :=
  {state with binding := (WHIRSourceObserver.privateReplay Q registry.iv
    (WHIRSourceRawCache.cache Q (rawState cap Q past)) seed source counted state.binding)}

/-- Replay chronological requests, updating source observations only from replies already completed at each prefix. Every header is frozen before adding that request's answer. -/
def replayPast (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) :
    ByteHistory Q → ByteHistory Q → AnchoredSourceRegistry.State cap → AnchoredSourceRegistry.State cap
  | [],past,state => updatePrefix registry Q seed source counted past state
  | (key,answer)::rest,past,state =>
      let state := updatePrefix registry Q seed source counted past state
      let state := AnchoredSourceRegistry.beforeRaw registry state key
      replayPast registry Q seed source counted rest ((key,answer)::past) state

theorem replayPast_preserves (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (remaining past : ByteHistory Q) (state : AnchoredSourceRegistry.State cap)
    (header : Header) (frozen : AnchoredSourceRegistry.Frozen) (known : state.headers header = some frozen) :
    (replayPast registry Q seed source counted remaining past state).headers header = some frozen := by
  induction remaining generalizing past state with
  | nil => exact known
  | cons item remaining ih =>
    exact ih _ _ (AnchoredSourceRegistry.beforeRaw_preserves registry
      (updatePrefix registry Q seed source counted past state) item.1 header frozen known)

theorem replayPast_extends (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (remaining past : ByteHistory Q) (state : AnchoredSourceRegistry.State cap) :
    CausalBindingState.Extends state.binding
      (replayPast registry Q seed source counted remaining past state).binding := by
  induction remaining generalizing past state with
  | nil => exact WHIRSourceObserver.privateReplay_extends Q registry.iv _ seed source counted state.binding
  | cons item remaining ih =>
    exact (WHIRSourceObserver.privateReplay_extends Q registry.iv _ seed source counted state.binding).trans
      ((AnchoredSourceRegistry.beforeRaw_binding_extends registry
        (updatePrefix registry Q seed source counted past state) item.1).trans (ih _ _))

/-- Once a query has recognized the original root and shape, every later completed-query/source replay keeps that same frozen capture. The answer of this first query is appended only after registration. -/
theorem chronological_first_query_freezes (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (key : RawKey Q) (answer : Digest32) (rest past : ByteHistory Q)
    (state : AnchoredSourceRegistry.State cap) (header : Header)
    (parsed : rawHeader registry key = some header) :
    ∃ frozen,
      (AnchoredSourceRegistry.beforeRaw registry (updatePrefix registry Q seed source counted past state) key).headers header =
        some frozen ∧
      (replayPast registry Q seed source counted ((key,answer)::rest) past state).headers header = some frozen := by
  obtain ⟨frozen,known⟩ := AnchoredSourceRegistry.beforeRaw_known registry
    (updatePrefix registry Q seed source counted past state) key header parsed
  exact ⟨frozen,known,replayPast_preserves registry Q seed source counted rest ((key,answer)::past) _ header frozen known⟩

noncomputable def preparedState (registry : Public) (p : Profile) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) (past : ByteHistory Q)
    (packet : Packet registry p Q) : AnchoredSourceRegistry.State cap :=
  AnchoredSourceRegistry.register
    (replayPast registry Q seed source counted past.reverse [] {}) (header registry p Q packet)

/-- This root and occupied shape are fixed before the fresh whole-run answer. The source's finite first-record hash is used, not a future primitive oracle lookup. -/
noncomputable def prepare (registry : Public) (p : Profile) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) (past : ByteHistory Q)
    (packet : Packet registry p Q) : AnchoredFiatShamirSecurity.PreAnchor p :=
  let h := header registry p Q packet
  let valid := (fromHistory_valid registry packet.val.history h (header_parsed registry p Q packet)).2.2.2
  let occupied : 0 < h.shape.lanes ∧ h.shape.lanes ≤ 2^(config p).folds[0]! :=
    ⟨valid.2.2.2.2.1,by rw [← header_batch registry p Q packet]; exact valid.2.2.2.2.2⟩
  let state := preparedState registry p Q seed source counted past packet
  ⟨h.shape.lanes,(CausalBindingState.capture state.binding p h.root h.shape.lanes occupied.2).base,occupied⟩

noncomputable def policy (registry : Public) (p : Profile) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (advertise : ByteHistory Q → Packet registry p Q → AnchoredFiatShamirSecurityCodec.Joint (config p).logN → E) :
    AnchoredByteStreamPrepared.Policy p Q registry.iv (accept registry p) :=
  ⟨prepare registry p Q seed source counted,advertise⟩

theorem prepare_list_bound (registry : Public) (p : Profile) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) (past : ByteHistory Q)
    (packet : Packet registry p Q) :
    (InitialCandidates.witnesses (config p) (prepare registry p Q seed source counted past packet).lanes
      (prepare registry p Q seed source counted past packet).root).card ≤ 2^32 :=
  InitialCandidates.production_witnesses_card p _ _

/-- Every requested block of this packet has exactly the same source header. Root preparation therefore works at the adversary's earliest queried block, not only when block zero is requested first. -/
theorem packet_key_header (registry : Public) (p : Profile) (Q : Nat) (packet : Packet registry p Q)
    (i : Fin (AnchoredFiatShamirSecurityCodec.blockCount (config p).logN)) :
    rawHeader registry (key packet.val i) = some (header registry p Q packet) := by
  rw [rawHeader,key_decodes]
  exact header_parsed registry p Q packet

end Whir.AnchoredSourceGroups
