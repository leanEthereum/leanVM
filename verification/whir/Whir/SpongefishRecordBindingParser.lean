import Whir.SpongefishCurrentModeQueries

/-! Current native record fields are read and compared in their real order.
Scalar reads are individual, not a grouped-vector rejection shortcut. This
successful/failed parse model does not assert Rust poison or error identity. -/
namespace Whir.SpongefishRecordBindingParser
open Concrete FiatShamirGame DuplexRefinement DuplexFraming
open SpongefishPCSRoundFrames SpongefishSessionAdapter
set_option autoImplicit false

abbrev Message := (kind : WireKind) × kind.Value

def Message.bytes (message : Message) : List Byte := message.1.codec.bytes message.2

def scalarMessages (values : List E) : List Message := values.map fun x => ⟨.scalar,x⟩

def messages (r : Record) : List Message :=
  scalarMessages (constants AnchoredHeaderCodec.openingMarker r.shape) ++
  [⟨.root,r.root⟩,⟨.root,r.context.cv⟩] ++ scalarMessages (contextScalars r.context) ++
  scalarMessages (pendingPacks r.context) ++ scalarMessages r.point ++ [⟨.scalar,r.value⟩]

theorem scalar_messages_bytes (values : List E) :
    (scalarMessages values).flatMap Message.bytes = scalarsBytes values := by
  rw [scalarMessages,List.flatMap_map]
  rfl

theorem messages_bytes (r : Record) : (messages r).flatMap Message.bytes = openingBytes r := by
  simp [messages,List.flatMap_append,scalar_messages_bytes,Message.bytes,WireKind.codec,
    Codec.bytes,rootCodec,scalarCodec,openingBytes,rawRoot,scalarBytes,List.append_assoc]

/-- Read first, compare second: a false field does not skip source absorption. -/
def checkedRead (c : Compression) (cur : Cursor) (message : Message) : Option Cursor :=
  match SpongefishPCSRoundFrames.read c cur message.1 with
  | none => none
  | some pair => if message.1.codec.bytes pair.2 = message.bytes then some pair.1 else none

def verifyFields (c : Compression) : Cursor → List Message → Option Cursor
  | cur,[] => some cur
  | cur,message::rest => do
    let next ← checkedRead c cur message
    verifyFields c next rest

def verify (c : Compression) (cur : Cursor) (r : Record) : Option Cursor :=
  verifyFields c cur (messages r)

def advance (c : Compression) (cur : Cursor) (message : Message) (rest : List Byte) : Cursor :=
  {cur with state := absorb c cur.state message.bytes, pending := SpongefishPCSRoundFrames.bind cur.pending message.bytes, narg := rest, bytesRead := cur.bytesRead+message.1.codec.size, messagesRead := cur.messagesRead+message.1.messages, events := cur.events ++ [.prover message.1 message.bytes]}

theorem checkedRead_append (c : Compression) (cur : Cursor) (message : Message) (rest : List Byte)
    (source : cur.narg = message.bytes ++ rest) :
    checkedRead c cur message = some (advance c cur message rest) := by
  rw [checkedRead,read_append c cur message.1 message.2 rest source]
  simp [advance,Message.bytes]

theorem checkedRead_exact (c : Compression) (cur next : Cursor) (message : Message) :
    checkedRead c cur message = some next ↔
      ∃ rest,cur.narg = message.bytes ++ rest ∧ next = advance c cur message rest := by
  constructor
  · intro accepted
    unfold checkedRead SpongefishPCSRoundFrames.read at accepted
    cases parsed : message.1.codec.parse cur.narg with
    | none => simp [parsed] at accepted
    | some pair =>
      rcases pair with ⟨value,rest⟩
      simp only [parsed] at accepted
      dsimp [Bind.bind,Option.bind,Pure.pure] at accepted
      split at accepted
      next equal =>
        simp only [Option.some.injEq] at accepted
        have source := Codec.canonical_read message.1.codec cur.narg rest value parsed
        rw [equal] at source
        exact ⟨rest,source,by simpa only [advance,equal] using accepted.symm⟩
      next different => contradiction
  · rintro ⟨rest,source,rfl⟩
    exact checkedRead_append c cur message rest source

theorem verifyFields_source (c : Compression) (cur : Cursor) (fields : List Message) :
    (∃ next,verifyFields c cur fields = some next) ↔
      ∃ rest,cur.narg = fields.flatMap Message.bytes ++ rest := by
  induction fields generalizing cur with
  | nil =>
    constructor
    · intro _
      exact ⟨cur.narg,rfl⟩
    · intro _
      exact ⟨cur,rfl⟩
  | cons message fields ih =>
    constructor
    · rintro ⟨next,accepted⟩
      simp only [verifyFields] at accepted
      obtain ⟨middle,step,tail⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨remaining,source,state⟩ := (checkedRead_exact c cur middle message).mp step
      obtain ⟨rest,after⟩ := (ih middle).mp ⟨next,tail⟩
      have middleNarg : middle.narg = remaining := by rw [state]; rfl
      rw [← middleNarg,after] at source
      exact ⟨rest,by simpa only [List.flatMap_cons,List.append_assoc] using source⟩
    · rintro ⟨rest,source⟩
      have before : cur.narg = message.bytes ++ (fields.flatMap Message.bytes ++ rest) := by
        simpa only [List.flatMap_cons,List.append_assoc] using source
      let middle := advance c cur message (fields.flatMap Message.bytes ++ rest)
      obtain ⟨next,tail⟩ := (ih middle).mpr ⟨rest,rfl⟩
      exact ⟨next,by
        rw [verifyFields,checkedRead_append c cur message _ before]
        exact tail⟩

theorem verify_source (c : Compression) (cur : Cursor) (r : Record) :
    (∃ next,verify c cur r = some next) ↔ ∃ rest,cur.narg = openingBytes r ++ rest := by
  rw [verify,verifyFields_source,messages_bytes]

theorem verifyFields_transport (c : Compression) (cur next : Cursor) (fields : List Message)
    (accepted : verifyFields c cur fields = some next) : Extends cur next := by
  induction fields generalizing cur with
  | nil =>
    simp only [verifyFields,Option.some.injEq] at accepted
    subst next
    exact extends_refl cur
  | cons message fields ih =>
    simp only [verifyFields] at accepted
    obtain ⟨middle,step,tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest,source,state⟩ := (checkedRead_exact c cur middle message).mp step
    have replay : replayCall c cur (.read message.1) = some middle := by
      rw [replayCall,read_append c cur message.1 message.2 rest source]
      simp only [Option.map_some]
      exact congrArg some state.symm
    exact extends_trans cur middle next (replayCall_transport c cur middle _ replay) (ih middle tail)

theorem verify_transport (c : Compression) (cur next : Cursor) (r : Record)
    (accepted : verify c cur r = some next) : Extends cur next :=
  verifyFields_transport c cur next (messages r) accepted

theorem verify_reject (c : Compression) (cur : Cursor) (r : Record)
    (different : ¬ ∃ rest,cur.narg = openingBytes r ++ rest) : verify c cur r = none := by
  cases result : verify c cur r with
  | none => rfl
  | some next => exact False.elim (different ((verify_source c cur r).mp ⟨next,result⟩))

/-- Successful checked reads are the actual individual source read replay. -/
theorem verifyFields_replay (c : Compression) (cur next : Cursor) (fields : List Message)
    (accepted : verifyFields c cur fields = some next) :
    replayCalls c cur (fields.map fun message => .read message.1) = some next := by
  induction fields generalizing cur with
  | nil => exact accepted
  | cons message fields ih =>
    simp only [verifyFields] at accepted
    obtain ⟨middle,step,tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest,source,state⟩ := (checkedRead_exact c cur middle message).mp step
    have replay : replayCall c cur (.read message.1) = some middle := by
      rw [replayCall,read_append c cur message.1 message.2 rest source]
      simp only [Option.map_some]
      exact congrArg some state.symm
    simp only [List.map_cons,replayCalls,replay]
    exact ih middle tail

theorem verify_bridge (c : Compression) (parameter : Digest32) (cur next : Cursor)
    (r : Record) (h : RepresentsCurrent c parameter cur.pending cur.state)
    (valid : SpongefishCurrentModeQueries.FrameDomain cur.pending)
    (accepted : verify c cur r = some next) :
    RepresentsCurrent c parameter next.pending next.state ∧
      SpongefishCurrentModeQueries.FrameDomain next.pending :=
  SpongefishCurrentModeQueries.all_round_frame_domain c parameter cur next
    ((messages r).map fun message => .read message.1) h valid
    (verifyFields_replay c cur next (messages r) accepted)

/-- A draw after the checked record has both its real bytes and a bounded
semantic address. Neither hidden CV equality nor supplied frame admissibility
is assumed for the resulting cursor. -/
theorem verify_draw_byte (c : Compression) (parameter : Digest32) (cur next : Cursor)
    (r : Record) (h : RepresentsCurrent c parameter cur.pending cur.state)
    (valid : SpongefishCurrentModeQueries.FrameDomain cur.pending)
    (accepted : verify c cur r = some next) (n : Nat) (positive : n ≠ 0)
    (t : State) (bytes : List Byte) (ok : squeeze c next.state n = .ok (t,bytes))
    (j : Nat) (within : j < n) :
    DuplexEncoding.Admissible
        (SpongefishCurrentModeQueries.coordinate next.pending ((next.pending.consumed+j)/32)) ∧
      bytes[j]'(by obtain ⟨_,len⟩ := squeeze_exact_cursor c next.state t n bytes ok; omega) =
        evalCoordinate c parameter
          (SpongefishCurrentModeQueries.coordinate next.pending ((next.pending.consumed+j)/32))
          ⟨(next.pending.consumed+j)%32,Nat.mod_lt _ (by decide)⟩ := by
  obtain ⟨represented,framed⟩ := verify_bridge c parameter cur next r h valid accepted
  exact ⟨SpongefishCurrentModeQueries.squeezed_coordinate_admissible c parameter
      next.pending next.state t represented framed n positive bytes ok j within,
    SpongefishCurrentModeQueries.squeezed_byte c parameter next.pending next.state t
      represented n positive bytes ok j within⟩

#print axioms verify_draw_byte

#print axioms verifyFields_replay
#print axioms verify_bridge

#print axioms verify_source
#print axioms verify_transport
#print axioms verify_reject

#print axioms messages_bytes
#print axioms checkedRead_append
#print axioms checkedRead_exact
end Whir.SpongefishRecordBindingParser
