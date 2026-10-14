import Whir.SpongefishCurrentRecordModeCapture

/-! Deterministic hand-port of the current #607 `commit.rs` preanchor header:
three individual F192 constants, then one raw32 root, before `verifier_messages`.
The public shape guard is the 64-bit source guard. This is not compiled Rust
correspondence, Rows constraint soundness, or a BLAKE2s/uniformity claim.
Malformed reads and mismatches return `none`; Rust error identity, retained
failed-read state and poisoning are deliberately not modeled. No anchor point,
anchor value, saved context, or previously trusted root is an input to recovery. -/
namespace Whir.SpongefishCurrentAnchorHeader
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishRecordBindingParser
set_option autoImplicit false

/-- Literal current header, not the historical five-scalar digest packing. -/
def bytes (shape : Shape) (root : Digest32) : List Byte := commitPrefix shape root

theorem bytes_length (shape : Shape) (root : Digest32) :
    (bytes shape root).length = 104 := commitPrefix_length shape root

def fields (shape : Shape) (root : Digest32) : List SpongefishRecordBindingParser.Message :=
  scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape) ++ [⟨.root,root⟩]

theorem fields_bytes (shape : Shape) (root : Digest32) :
    (fields shape root).flatMap Message.bytes = bytes shape root := by
  rw [fields,List.flatMap_append,scalar_messages_bytes]
  rfl

/-- Canonical constants are checked; the raw root is decoded, never compared
against a supplied root. Insufficient transport has no fake valid fallback. -/
def decode (shape : Shape) (source : List Byte) : Option (Digest32 × List Byte) := do
  if ¬ shape.Valid then none else do
    let (header,rest) ← SpongefishCurrentRecordDecoder.scalars 3 source
    if header ≠ constants AnchoredHeaderCodec.anchorMarker shape then none else
      rootCodec.parse rest

theorem decode_encoded (shape : Shape) (valid : shape.Valid) (root : Digest32)
    (rest : List Byte) : decode shape (bytes shape root ++ rest) = some (root,rest) := by
  unfold decode bytes commitPrefix
  simp only [valid,not_true_eq_false,↓reduceIte,List.append_assoc]
  rw [show 3 = (constants AnchoredHeaderCodec.anchorMarker shape).length from rfl,
    SpongefishCurrentRecordDecoder.scalars_encoded]
  dsimp only [Bind.bind,Option.bind]
  simp only [ne_eq,not_true_eq_false,↓reduceIte]
  exact Codec.parse_append rootCodec root rest

theorem decode_source (shape : Shape) (source rest : List Byte) (root : Digest32)
    (accepted : decode shape source = some (root,rest)) :
    shape.Valid ∧ source = bytes shape root ++ rest := by
  unfold decode at accepted
  split at accepted
  · contradiction
  · rename_i valid
    obtain ⟨⟨header,after⟩,readHeader,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    split at accepted
    · contradiction
    · rename_i equal
      have canonical := (SpongefishCurrentRecordDecoder.scalars_source 3 source after header readHeader).2
      have rootSource := Codec.canonical_read rootCodec after rest root accepted
      have matchHeader : header = constants AnchoredHeaderCodec.anchorMarker shape := by
        simpa only [ne_eq,not_not] using equal
      rw [matchHeader,rootSource] at canonical
      exact ⟨by simpa using valid,by simpa [bytes,commitPrefix,Codec.bytes,rootCodec,
        rawRoot,List.append_assoc] using canonical⟩

theorem decode_exact (shape : Shape) (source rest : List Byte) (root : Digest32) :
    decode shape source = some (root,rest) ↔
      shape.Valid ∧ source = bytes shape root ++ rest := by
  constructor
  · exact decode_source shape source rest root
  · rintro ⟨valid,rfl⟩; exact decode_encoded shape valid root rest

/-- Exactly the last 104 bytes, with no uniqueness assumption or candidate scan. -/
def suffix (shape : Shape) (source : List Byte) : Option Digest32 := do
  let (root,rest) ← decode shape (source.drop (source.length-104))
  if rest = [] then some root else none

theorem suffix_recovery (shape : Shape) (valid : shape.Valid) (root : Digest32)
    (pre : List Byte) : suffix shape (pre ++ bytes shape root) = some root := by
  unfold suffix
  simp only [List.length_append,bytes_length,Nat.add_sub_cancel_right,List.drop_left]
  have parsed := decode_encoded shape valid root []
  simp only [List.append_nil] at parsed
  rw [parsed]
  rfl

theorem suffix_source (shape : Shape) (source : List Byte) (root : Digest32)
    (accepted : suffix shape source = some root) :
    shape.Valid ∧ List.IsSuffix (bytes shape root) source := by
  unfold suffix at accepted
  cases parsed : decode shape (source.drop (source.length-104)) with
  | none => simp [parsed] at accepted
  | some pair =>
    obtain ⟨actual,rest⟩ := pair
    simp only [parsed] at accepted
    change (if rest = [] then some actual else none) = some root at accepted
    split at accepted
    · rename_i empty
      cases accepted
      obtain ⟨valid,canonical⟩ := decode_source shape _ rest root parsed
      rw [empty,List.append_nil] at canonical
      exact ⟨valid,source.take (source.length-104),by
        rw [← canonical]; exact List.take_append_drop _ source⟩
    · contradiction

theorem suffix_unique (shape : Shape) (valid : shape.Valid) (root other : Digest32)
    (pre : List Byte) (accepted : suffix shape (pre ++ bytes shape root) = some other) :
    other = root := by
  exact Option.some.inj (accepted.symm.trans (suffix_recovery shape valid root pre))

/-- Actual individual verifier calls: three checked scalar reads followed by
an unchecked raw32 root read. The root is selected before any verifier answer. -/
def readHeader (c : Compression) (cur : Cursor) (shape : Shape) :
    Option (Cursor × Digest32) := do
  if ¬ shape.Valid then none else do
    let next ← verifyFields c cur (scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape))
    SpongefishPCSRoundFrames.read c next .root

private theorem raw_read_exact (c : Compression) (cur next : Cursor) (root : Digest32) :
    SpongefishPCSRoundFrames.read c cur .root = some (next,root) ↔
      checkedRead c cur ⟨.root,root⟩ = some next := by
  constructor
  · intro accepted
    unfold SpongefishPCSRoundFrames.read at accepted
    cases parsed : rootCodec.parse cur.narg with
    | none => simp [WireKind.codec,parsed] at accepted
    | some pair =>
      obtain ⟨actual,rest⟩ := pair
      simp only [WireKind.codec,parsed] at accepted
      dsimp only [Bind.bind,Option.bind,Pure.pure] at accepted
      have equality : (advance c cur ⟨.root,actual⟩ rest,actual) = (next,root) :=
        Option.some.inj accepted
      have actualEq : actual = root := congrArg Prod.snd equality
      have cursorEq : next = advance c cur ⟨.root,actual⟩ rest :=
        (congrArg Prod.fst equality).symm
      have canonical := Codec.canonical_read rootCodec cur.narg rest actual parsed
      apply (checkedRead_exact c cur next ⟨.root,root⟩).mpr
      refine ⟨rest,?_,?_⟩
      · change cur.narg = rootCodec.bytes root ++ rest
        rw [← actualEq]
        exact canonical
      · rw [← actualEq]
        exact cursorEq
  · intro accepted
    obtain ⟨rest,source,rfl⟩ := (checkedRead_exact c cur next ⟨.root,root⟩).mp accepted
    exact read_append c cur .root root rest source

private theorem verifyFields_append (c : Compression) (cur : Cursor)
    (a b : List SpongefishRecordBindingParser.Message) :
    verifyFields c cur (a ++ b) = (verifyFields c cur a).bind (fun next => verifyFields c next b) := by
  induction a generalizing cur with
  | nil => rfl
  | cons message a ih =>
    change ((checkedRead c cur message).bind (fun middle => verifyFields c middle (a ++ b))) =
      (((checkedRead c cur message).bind (fun middle => verifyFields c middle a)).bind
        (fun next => verifyFields c next b))
    cases checkedRead c cur message with
    | none => rfl
    | some middle => exact ih middle

theorem readHeader_exact (c : Compression) (cur next : Cursor) (shape : Shape)
    (root : Digest32) : readHeader c cur shape = some (next,root) ↔
      shape.Valid ∧ verifyFields c cur (fields shape root) = some next := by
  unfold readHeader
  by_cases valid : shape.Valid
  · simp only [valid,not_true_eq_false,↓reduceIte,true_and,fields,verifyFields_append]
    cases result : verifyFields c cur (scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape)) with
    | none => simp
    | some middle =>
      change SpongefishPCSRoundFrames.read c middle .root = some (next,root) ↔
        verifyFields c middle [⟨.root,root⟩] = some next
      have singleton : verifyFields c middle [⟨.root,root⟩] =
          checkedRead c middle ⟨.root,root⟩ := by
        simp only [verifyFields]
        cases checkedRead c middle ⟨.root,root⟩ <;> rfl
      rw [singleton]
      exact raw_read_exact c middle next root
  · simp [valid]

/-- There are no grouped scalar reads and no draw in the header replay. -/
theorem readHeader_replay (c : Compression) (cur next : Cursor) (shape : Shape)
    (root : Digest32) (accepted : readHeader c cur shape = some (next,root)) :
    replayCalls c cur [.read .scalar,.read .scalar,.read .scalar,.read .root] = some next := by
  have verified := ((readHeader_exact c cur next shape root).mp accepted).2
  exact verifyFields_replay c cur next (fields shape root) verified

/-- Remainder, read counters and public event history are derived from reads. -/
private theorem fields_facts (c : Compression) (cur next : Cursor)
    (ms : List SpongefishRecordBindingParser.Message)
    (accepted : verifyFields c cur ms = some next) :
    cur.narg = ms.flatMap Message.bytes ++ next.narg ∧
    next.bytesRead = cur.bytesRead + (ms.map fun m => m.1.codec.size).sum ∧
    next.messagesRead = cur.messagesRead + (ms.map fun m => m.1.messages).sum ∧
    next.events = cur.events ++ (ms.map fun m => SourceEvent.prover m.1 m.bytes) ∧
    next.state = absorb c cur.state (ms.flatMap Message.bytes) := by
  induction ms generalizing cur with
  | nil =>
    simp only [verifyFields,Option.some.injEq] at accepted
    cases accepted
    simp
  | cons message ms ih =>
    simp only [verifyFields] at accepted
    obtain ⟨middle,step,tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest,source,state⟩ := (checkedRead_exact c cur middle message).mp step
    have facts := ih middle tail
    rw [state] at facts
    dsimp only [advance] at facts
    obtain ⟨remaining,byteCount,messageCount,events,absorbed⟩ := facts
    exact ⟨by rw [source,remaining]; simp [List.flatMap_cons,List.append_assoc],
      by simpa [List.map_cons,List.sum_cons,Nat.add_assoc] using byteCount,
      by simpa [List.map_cons,List.sum_cons,Nat.add_assoc] using messageCount,
      by simpa [List.map_cons,List.append_assoc] using events,
      by simpa [List.flatMap_cons,absorb_append] using absorbed⟩

theorem readHeader_facts (c : Compression) (cur next : Cursor) (shape : Shape)
    (root : Digest32) (accepted : readHeader c cur shape = some (next,root)) :
    shape.Valid ∧ cur.narg = bytes shape root ++ next.narg ∧
    next.bytesRead = cur.bytesRead + 104 ∧ next.messagesRead = cur.messagesRead + 4 ∧
    next.events = cur.events ++ (fields shape root).map (fun m => SourceEvent.prover m.1 m.bytes) ∧
    next.state = absorb c cur.state (bytes shape root) ∧
    next.pending.run = cur.pending.run ++ bytes shape root := by
  obtain ⟨valid,verified⟩ := (readHeader_exact c cur next shape root).mp accepted
  obtain ⟨source,byteCount,messageCount,events,state⟩ := fields_facts c cur next _ verified
  rw [fields_bytes] at source state
  have run := SpongefishCurrentRecordModeCapture.verifyFields_run c cur next _ verified
  rw [fields_bytes] at run
  refine ⟨valid,source,?_,?_,events,state,run⟩
  · change next.bytesRead = cur.bytesRead + 104 at byteCount
    exact byteCount
  · change next.messagesRead = cur.messagesRead + 4 at messageCount
    exact messageCount

theorem readHeader_decoder (c : Compression) (cur next : Cursor) (shape : Shape)
    (root : Digest32) (accepted : readHeader c cur shape = some (next,root)) :
    decode shape cur.narg = some (root,next.narg) := by
  obtain ⟨valid,source,_⟩ := readHeader_facts c cur next shape root accepted
  exact (decode_exact shape cur.narg next.narg root).mpr ⟨valid,source⟩

/-- Complete successful-header domain. Invalid public shapes, mismatched
constants and truncated headers cannot enter the successful read semantics. -/
theorem readHeader_source (c : Compression) (cur : Cursor) (shape : Shape)
    (root : Digest32) :
    (∃ next,readHeader c cur shape = some (next,root)) ↔
      shape.Valid ∧ ∃ rest,cur.narg = bytes shape root ++ rest := by
  constructor
  · rintro ⟨next,accepted⟩
    obtain ⟨valid,source,_⟩ := readHeader_facts c cur next shape root accepted
    exact ⟨valid,next.narg,source⟩
  · rintro ⟨valid,rest,source⟩
    have before : cur.narg = (fields shape root).flatMap Message.bytes ++ rest := by
      rw [fields_bytes]
      exact source
    obtain ⟨next,verified⟩ := (verifyFields_source c cur (fields shape root)).mpr ⟨rest,before⟩
    exact ⟨next,(readHeader_exact c cur next shape root).mpr ⟨valid,verified⟩⟩

/-- Recover the header from the last closed absorb body, irrespective of all
prior absorb bytes and preceding output consumption. -/
def fromHistory (shape : Shape) (history : FramedHistory) : Option Digest32 :=
  match history.frames.getLast? with
  | some (.absorb _ source) => suffix shape source
  | _ => none

theorem closed_header (m : Pending) (shape : Shape) (valid : shape.Valid)
    (root : Digest32) (pre : List Byte) (run : m.run = pre ++ bytes shape root) :
    fromHistory shape (close m).core.history = some root := by
  have nonempty : m.run ≠ [] := by
    intro empty
    have len := congrArg List.length (run.symm.trans empty)
    simp only [List.length_append,List.length_nil,bytes_length] at len
    omega
  simp only [fromHistory,close,nonempty,↓reduceIte,Pending.core,List.map_append,
    List.map_singleton,ByteFrame.historicalCore,List.getLast?_append,List.getLast?_singleton]
  change suffix shape m.run = some root
  rw [run]
  exact suffix_recovery shape valid root pre

def rawHeader {Q : Nat} (shape : Shape) (iv : Digest32) (raw : RawKey Q) : Option Digest32 :=
  (WHIRHeaderRoots.decodeRaw iv raw).bind (fun q => fromHistory shape q.history)

theorem rawHeader_sound {Q : Nat} (shape : Shape) (iv : Digest32) (raw : RawKey Q)
    (root : Digest32) (accepted : rawHeader shape iv raw = some root) :
    ∃ q : Coordinate, ∃ bound : pathCost q ≤ Q,
      DuplexEncoding.Admissible q ∧ constructionKey Q iv q bound = raw ∧
      ∃ previous source, q.history.frames.getLast? = some (.absorb previous source) ∧
        shape.Valid ∧ List.IsSuffix (bytes shape root) source := by
  obtain ⟨q,decoded,parsed⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨bound,valid,key⟩ := WHIRHeaderRoots.decodeRaw_sound iv raw q decoded
  refine ⟨q,bound,valid,key,?_⟩
  unfold fromHistory at parsed
  split at parsed
  · rename_i previous source last
    obtain ⟨shapeValid,sourceSuffix⟩ := suffix_source shape source root parsed
    exact ⟨previous,source,last,shapeValid,sourceSuffix⟩
  · contradiction

/-- Actual next nonempty anchor group, every returned byte, and an exact whole
bounded raw key. Only the prior representation/frame geometry and total path
budget are hypotheses; output uniformity, fixed CV, root equality, later anchor
point/value and trusted parser matching are not. -/
theorem readHeader_anchor_byte {Q : Nat} (c : Compression) (iv : Digest32)
    (cur next : Cursor) (shape : Shape) (root : Digest32)
    (accepted : readHeader c cur shape = some (next,root))
    (represented : RepresentsCurrent c iv cur.pending cur.state)
    (framed : SpongefishCurrentModeQueries.FrameDomain cur.pending)
    (state : State) (output : List Byte)
    (squeezed : squeeze c next.state (24*shape.logN) = .ok (state,output))
    (j : Nat) (within : j < 24*shape.logN)
    (work : pathCost (SpongefishCurrentModeQueries.coordinate next.pending
      ((next.pending.consumed+j)/32)) ≤ Q) :
    let q := SpongefishCurrentModeQueries.coordinate next.pending ((next.pending.consumed+j)/32)
    DuplexEncoding.Admissible q ∧
      rawHeader shape iv (constructionKey Q iv q work) = some root ∧
      output[j]'(by obtain ⟨_,len⟩ := squeeze_exact_cursor c next.state state _ output squeezed; omega) =
        evalCoordinate c iv q ⟨(next.pending.consumed+j)%32,Nat.mod_lt _ (by decide)⟩ := by
  obtain ⟨valid,verified⟩ := (readHeader_exact c cur next shape root).mp accepted
  obtain ⟨afterRep,afterFrame⟩ := SpongefishCurrentModeQueries.all_round_frame_domain c iv cur next
    ((fields shape root).map fun message => .read message.1) represented framed
    (verifyFields_replay c cur next _ verified)
  have positive : 24*shape.logN ≠ 0 := by have := valid.1; omega
  have admissible := SpongefishCurrentModeQueries.squeezed_coordinate_admissible c iv next.pending
    next.state state afterRep afterFrame _ positive output squeezed j within
  refine ⟨admissible,?_,SpongefishCurrentModeQueries.squeezed_byte c iv next.pending
    next.state state afterRep _ positive output squeezed j within⟩
  rw [rawHeader,WHIRHeaderRoots.decodeRaw_construction iv _ admissible work]
  simp only [Option.bind_some,SpongefishCurrentModeQueries.coordinate]
  have run := SpongefishCurrentRecordModeCapture.verifyFields_run c cur next _ verified
  rw [fields_bytes] at run
  exact closed_header next.pending shape valid root cur.pending.run run

#print axioms bytes_length
#print axioms fields_bytes
#print axioms decode_encoded
#print axioms decode_source
#print axioms decode_exact
#print axioms suffix_recovery
#print axioms suffix_source
#print axioms suffix_unique
#print axioms readHeader_exact
#print axioms readHeader_replay
#print axioms readHeader_facts
#print axioms readHeader_decoder
#print axioms readHeader_source
#print axioms closed_header
#print axioms rawHeader_sound
#print axioms readHeader_anchor_byte
end Whir.SpongefishCurrentAnchorHeader
