import Whir.SpongefishCurrentRecordDecoder
import Whir.WHIRHeaderRoots

/-! Current opening-record root references are recovered from the actual last
closed absorb body. These are deterministic hand-port transport results, not
Rust acceptance or a completed current native knowledge composition. -/
namespace Whir.SpongefishCurrentRecordModeCapture
open Concrete FiatShamirGame DuplexRefinement DuplexFraming
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishRecordBindingParser
set_option autoImplicit false

theorem bind_run (m : Pending) (bytes : List Byte) :
    (SpongefishPCSRoundFrames.bind m bytes).run = m.run ++ bytes := by
  by_cases empty : bytes = [] <;> simp [SpongefishPCSRoundFrames.bind,empty]

theorem verifyFields_run (c : Compression) (cur next : Cursor)
    (fields : List SpongefishRecordBindingParser.Message)
    (accepted : verifyFields c cur fields = some next) :
    next.pending.run = cur.pending.run ++ fields.flatMap Message.bytes := by
  induction fields generalizing cur with
  | nil => simp only [verifyFields,Option.some.injEq] at accepted; cases accepted; simp
  | cons message fields ih =>
    simp only [verifyFields] at accepted
    obtain ⟨middle,step,tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest,_,state⟩ := (checkedRead_exact c cur middle message).mp step
    have later := ih middle tail
    rw [state] at later
    simpa only [advance,bind_run,List.flatMap_cons,List.append_assoc] using later

theorem verify_run (c : Compression) (cur next : Cursor) (r : Record)
    (accepted : verify c cur r = some next) :
    next.pending.run = cur.pending.run ++ openingBytes r := by
  simpa only [messages_bytes] using verifyFields_run c cur next (messages r) accepted

/-- Only public frame bytes are inspected. All bounded suffix candidates are
retained; there is no unproved first-match selection. -/
def records (shape : AnchoredHeaderCodec.Shape) (history : FramedHistory) : List Record :=
  match history.frames.getLast? with
  | some (.absorb _ bytes) => SpongefishCurrentRecordDecoder.suffixCandidates shape bytes
  | _ => []

theorem records_length (shape : AnchoredHeaderCodec.Shape) (history : FramedHistory) :
    (records shape history).length ≤ 4 := by
  unfold records
  split
  · exact SpongefishCurrentRecordDecoder.suffixCandidates_length _ _
  · simp

theorem closed_record (m : Pending) (r : Record) (pre : List Byte)
    (run : m.run = pre ++ openingBytes r) (valid : r.shape.Valid)
    (pending : r.context.pending.length ≤ 64) (point : r.point.length = r.shape.logN) :
    r ∈ records r.shape (close m).core.history := by
  have nonempty : m.run ≠ [] := by
    intro empty
    have len := congrArg List.length (run.symm.trans empty)
    simp only [List.length_append,List.length_nil,openingBytes_length] at len
    omega
  simp only [records,close,nonempty,↓reduceIte,Pending.core,List.map_append,
    List.map_singleton,ByteFrame.historicalCore,List.getLast?_append,List.getLast?_singleton]
  change r ∈ SpongefishCurrentRecordDecoder.suffixCandidates r.shape m.run
  rw [run]
  exact SpongefishCurrentRecordDecoder.suffixCandidates_recovery r valid pending point pre

theorem verified_record_coordinate (c : Compression) (cur next : Cursor) (r : Record)
    (accepted : verify c cur r = some next) (valid : r.shape.Valid)
    (pending : r.context.pending.length ≤ 64) (point : r.point.length = r.shape.logN)
    (block : Nat) :
    r ∈ records r.shape (SpongefishCurrentModeQueries.coordinate next.pending block).history := by
  exact closed_record next.pending r cur.pending.run (verify_run c cur next r accepted)
    valid pending point

/-- Exact reconstruction checks the whole raw coordinate, including IV and
template bits, before any current record bytes become root references. -/
def rawRecords {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32)
    (raw : DuplexModeGame.RawKey Q) : List Record :=
  match WHIRHeaderRoots.decodeRaw iv raw with
  | none => []
  | some q => records shape q.history

theorem rawRecords_length {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32)
    (raw : DuplexModeGame.RawKey Q) : (rawRecords shape iv raw).length ≤ 4 := by
  unfold rawRecords
  split
  · simp
  · exact records_length _ _

theorem rawRecords_sound {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32)
    (raw : DuplexModeGame.RawKey Q) (r : Record) (member : r ∈ rawRecords shape iv raw) :
    ∃ q : Coordinate, ∃ bound : pathCost q ≤ Q,
      DuplexEncoding.Admissible q ∧ DuplexModeGame.constructionKey Q iv q bound = raw ∧
      r ∈ records shape q.history := by
  unfold rawRecords at member
  cases decoded : WHIRHeaderRoots.decodeRaw iv raw with
  | none => simp [decoded] at member
  | some q =>
    simp only [decoded] at member
    obtain ⟨bound,valid,exactKey⟩ := WHIRHeaderRoots.decodeRaw_sound iv raw q decoded
    exact ⟨q,bound,valid,exactKey,member⟩

#print axioms rawRecords_sound

theorem rawRecords_construction {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (bound : pathCost q ≤ Q) :
    rawRecords shape iv (DuplexModeGame.constructionKey Q iv q bound) = records shape q.history := by
  rw [rawRecords,WHIRHeaderRoots.decodeRaw_construction iv q valid bound]

theorem verified_raw_record {Q : Nat} (c : Compression) (cur next : Cursor) (r : Record)
    (accepted : verify c cur r = some next) (valid : r.shape.Valid)
    (pending : r.context.pending.length ≤ 64) (point : r.point.length = r.shape.logN)
    (block : Nat) (iv : Digest32)
    (framed : SpongefishCurrentModeQueries.FrameDomain next.pending) (bounded : block < 2^44)
    (work : pathCost (SpongefishCurrentModeQueries.coordinate next.pending block) ≤ Q) :
    r ∈ rawRecords r.shape iv (DuplexModeGame.constructionKey Q iv
      (SpongefishCurrentModeQueries.coordinate next.pending block) work) := by
  rw [rawRecords_construction _ _ _ (SpongefishCurrentModeQueries.coordinate_admissible
    next.pending framed block bounded) work]
  exact verified_record_coordinate c cur next r accepted valid pending point block

#print axioms rawRecords_length
#print axioms rawRecords_construction
#print axioms verified_raw_record

#print axioms bind_run
#print axioms verifyFields_run
#print axioms verify_run
#print axioms records_length
#print axioms closed_record
#print axioms verified_record_coordinate
end Whir.SpongefishCurrentRecordModeCapture
