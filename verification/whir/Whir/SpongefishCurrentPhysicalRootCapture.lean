import Whir.SpongefishCurrentCommitmentReceive
import Whir.PCSBCSPublicExtractor

/-! Current #607 raw-header capture at PR600 75d4562bde1efe296b4e32d2a195fdfc232b3ead.
This is an executable public hand-port, not compiler/Rust equivalence. Unlike the
historical packet recognizer, it reads three scalar constants and a raw32 root
from the last closed absorb frame of an exact bounded output key. No saved
record, answer, opening tape, or final-log completion is an input to recognition.

Physical dimensions follow commit.rs:335-347 and verify.rs:379-405: height is
logN-logBatch+logRate, full leaf width is 2^logBatch, occupied width is lanes.
merkle.rs:167-174,589-590 hashes zeros(full-occupied) || row; verifier.rs:116-117,
152-158 removes the prefix only after authentication. The getter below uses the
existing full-image sourceCells/freeze path, never hashes a compact row instead.
Malformed keys/headers fail; missing images remain unavailable with rectangular
numerical defaults, not authenticated fallback leaves. Error identity/poisoning,
native event instrumentation and the original knowledge-statement join are not
asserted here. -/
namespace Whir.SpongefishCurrentPhysicalRootCapture
open Concrete FiatShamirGame DuplexFraming DuplexModeGame SpongefishSessionAdapter
open SpongefishPCSRoundFrames SpongefishRecordBindingParser PCSBCSSourceRootReferences
open PublicMerkleLog PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open DuplexRefinement TypedOracleCompiler
set_option autoImplicit false

/-- One fixed physical shape, derived from the actual expected header shape. -/
def physicalShape (shape : SpongefishSessionAdapter.Shape) : PCSBCSMerkleRootCache.Shape :=
  initialShape shape

def reference (shape : SpongefishSessionAdapter.Shape) (root : Digest32) : Reference :=
  ⟨root,physicalShape shape⟩

theorem physical_shape (shape : SpongefishSessionAdapter.Shape) :
    (physicalShape shape).height = shape.logN-shape.logBatch+shape.logRate ∧
    (physicalShape shape).leafWords = 2^shape.logBatch ∧
    (physicalShape shape).occupied = shape.lanes := ⟨rfl,rfl,rfl⟩

theorem occupied_guard (shape : SpongefishSessionAdapter.Shape) (valid : shape.Valid) :
    1 ≤ (physicalShape shape).occupied ∧
    (physicalShape shape).occupied ≤ (physicalShape shape).leafWords ∧
    0 < (physicalShape shape).height ∧ (physicalShape shape).height < 64 := by
  rcases valid with ⟨batch,n,rate,height,lanes,fits⟩
  change 1 ≤ shape.lanes ∧ shape.lanes ≤ 2^shape.logBatch ∧
    0 < shape.logN-shape.logBatch+shape.logRate ∧
    shape.logN-shape.logBatch+shape.logRate < 64
  exact ⟨lanes,fits,by omega,height⟩

/-- Output-key recognition only: exact IV/template/path bound first, literal
current canonical suffix second. It deliberately permits an adversarial earlier
output-key mention, without requiring a current-root-firstMention certificate. -/
def recognize {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (raw : PublicCompressionCouplingMixed.Key B) : Option Reference :=
  match raw with
  | .inl _ => none
  | .inr key => do
    let q ← WHIRHeaderRoots.decodeRaw iv key
    match q.terminal with
    | .output _ => (SpongefishCurrentAnchorHeader.fromHistory shape q.history).map (reference shape)
    | _ => none

def addresses {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (raw : PublicCompressionCouplingMixed.Key B) : List Reference :=
  (recognize shape iv raw).toList

theorem recognize_output {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (work : pathCost q ≤ B)
    (block : Nat) (terminal : q.terminal = .output block) (root : Digest32)
    (header : SpongefishCurrentAnchorHeader.fromHistory shape q.history = some root) :
    recognize shape iv (.inr (constructionKey B iv q work)) = some (reference shape root) := by
  simp [recognize,WHIRHeaderRoots.decodeRaw_construction iv q valid work,terminal,header]

theorem recognize_rawHeader {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (work : pathCost q ≤ B)
    (block : Nat) (terminal : q.terminal = .output block) (root : Digest32)
    (header : SpongefishCurrentAnchorHeader.rawHeader shape iv
      (constructionKey B iv q work) = some root) :
    recognize shape iv (.inr (constructionKey B iv q work)) = some (reference shape root) := by
  have parsed : SpongefishCurrentAnchorHeader.fromHistory shape q.history = some root := by
    simpa only [SpongefishCurrentAnchorHeader.rawHeader,
      WHIRHeaderRoots.decodeRaw_construction iv q valid work,Option.bind_some] using header
  exact recognize_output shape iv q valid work block terminal root parsed

theorem recognize_sound {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (raw : PublicCompressionCouplingMixed.Key B) (ref : Reference)
    (found : recognize shape iv raw = some ref) :
    ∃ key q, ∃ work : pathCost q ≤ B, ∃ block previous source,
      raw = .inr key ∧ DuplexEncoding.Admissible q ∧
      constructionKey B iv q work = key ∧ q.terminal = .output block ∧
      q.history.frames.getLast? = some (.absorb previous source) ∧
      shape.Valid ∧ List.IsSuffix (SpongefishCurrentAnchorHeader.bytes shape ref.root) source ∧
      ref.shape = physicalShape shape := by
  cases raw with
  | inl input => simp [recognize] at found
  | inr key =>
    obtain ⟨q,decoded,found⟩ := Option.bind_eq_some_iff.mp found
    cases terminal : q.terminal with
    | commitment consumed => simp [terminal] at found
    | powBase consumed difficulty => simp [terminal] at found
    | output block =>
      simp only [terminal] at found
      obtain ⟨root,parsed,equal⟩ := Option.map_eq_some_iff.mp found
      subst ref
      have rawHeader : SpongefishCurrentAnchorHeader.rawHeader shape iv key = some root := by
        simp [SpongefishCurrentAnchorHeader.rawHeader,decoded,parsed]
      obtain ⟨other,work,valid,keyEq,previous,source,last,shapeValid,suffix⟩ :=
        SpongefishCurrentAnchorHeader.rawHeader_sound shape iv key root rawHeader
      have otherEq : other = q := by
        have otherDecoded := WHIRHeaderRoots.decodeRaw_construction iv other valid work
        rw [keyEq,decoded] at otherDecoded
        exact (Option.some.inj otherDecoded).symm
      subst other
      exact ⟨key,q,work,block,previous,source,rfl,valid,keyEq,terminal,last,shapeValid,suffix,rfl⟩

/-- Includes wrong IV/template/holes/flags/lengths and over-budget geometry. -/
theorem malformed_key_rejected {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (key : RawKey B) (bad : WHIRHeaderRoots.decodeRaw iv key = none) :
    recognize shape iv (.inr key) = none := by simp [recognize,bad]

theorem malformed_header_rejected {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (key : RawKey B) (q : Coordinate)
    (decoded : WHIRHeaderRoots.decodeRaw iv key = some q)
    (bad : SpongefishCurrentAnchorHeader.fromHistory shape q.history = none) :
    recognize shape iv (.inr key) = none := by
  simp only [recognize,decoded]
  change (match q.terminal with
    | .output _ => (SpongefishCurrentAnchorHeader.fromHistory shape q.history).map (reference shape)
    | _ => none) = none
  cases terminal : q.terminal <;> simp [bad]

theorem invalid_shape_rejected {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (raw : PublicCompressionCouplingMixed.Key B) (invalid : ¬ shape.Valid) :
    recognize shape iv raw = none := by
  cases found : recognize shape iv raw with
  | none => rfl
  | some ref =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,valid,_,_⟩ := recognize_sound shape iv raw ref found
    exact (invalid valid).elim

/-- Every actual sampled-point byte of a successful current receive discloses
its fixed-shape root address at the corresponding literal preanswer output key.
The representation, frame domain and per-key path cap remain explicit. -/
theorem receive_membership {B : Nat} (c : Compression) (iv : Digest32)
    (cur next : Cursor) (shape : SpongefishSessionAdapter.Shape) (r : Record)
    (accepted : SpongefishCurrentCommitmentReceive.receive c cur shape = some (next,r))
    (represented : RepresentsCurrent c iv cur.pending cur.state)
    (framed : SpongefishCurrentModeQueries.FrameDomain cur.pending) :
    ∃ header sampled bytes, ∃ (point : Fin shape.logN → E),
      SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,r.root) ∧
      bytes = (vectorCodec shape.logN).bytes point ∧ r.point = List.ofFn point ∧
      read c sampled .scalar = some (next,r.value) ∧
      ∀ (j : Nat) (_within : j < 24*shape.logN)
        (work : pathCost (SpongefishCurrentModeQueries.coordinate header.pending
          ((header.pending.consumed+j)/32)) ≤ B),
        reference shape r.root ∈ addresses shape iv (.inr (constructionKey B iv
          (SpongefishCurrentModeQueries.coordinate header.pending
            ((header.pending.consumed+j)/32)) work)) := by
  obtain ⟨header,sampled,bytes,point,readHeader,encoded,pointEq,readValue,squeezed,source⟩ :=
    SpongefishCurrentCommitmentReceive.receive_anchor_source (Q := B) c iv cur next shape r
      accepted represented framed
  refine ⟨header,sampled,bytes,point,readHeader,encoded,pointEq,readValue,?_⟩
  intro j within work
  obtain ⟨valid,parsed,_⟩ := source j within work
  have found := recognize_rawHeader shape iv _ valid work _ rfl r.root parsed
  simp [addresses,found]

abbrev Event (B : Nat) := Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)

def firstPrefix {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (ref : Reference) (events : List (Event B)) : Option (List (Event B)) :=
  PCSBCSNativePublicCapture.firstPrefix (addresses shape iv) ref events

def ordinaryStep {B : Nat} (log : PublicLog) (event : Event B) : PublicLog :=
  match event.1 with
  | .inl input => (input,event.2) :: log
  | .inr _ => log

/-- Convert only completed ordinary draws in the captured prefix. Raw output
answers are not ordinary Merkle hashes, and the triggering answer is absent. -/
def ordinaryLog {B : Nat} (events : List (Event B)) : PublicLog :=
  events.foldl ordinaryStep []

def capture {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (ref : Reference) (events : List (Event B)) : Option Frozen :=
  (firstPrefix shape iv ref events).map (fun before => freeze (ordinaryLog before) ref.root ref.shape)

def root0 {B : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (ref : Reference) (events : List (Event B)) : Option (Array (Array K)) :=
  (capture shape iv ref events).map Frozen.raw

/-- General execution join: this is the actual adaptive trace, not a supplied
firstMention certificate. It applies to every current-key sampling program. -/
theorem firstPrefix_source {B n : Nat} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (iv : Digest32) (ref : Reference)
    (program : Sampling (PublicCompressionCouplingMixed.Key B) (fun _ => Digest32) R n)
    (table : PublicCompressionCouplingMixed.Key B → Digest32) :
    PCSBCSFirstRootDisclosure.firstMention (addresses shape iv) ref program table =
      firstPrefix shape iv ref (Sampling.execute table program).2 :=
  PCSBCSNativePublicCapture.firstPrefix_execute _ _ _ _

theorem firstPrefix_extension {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (events before later : List (Event B))
    (found : firstPrefix shape iv ref events = some before) :
    firstPrefix shape iv ref (events ++ later) = some before := by
  induction events generalizing before with
  | nil => simp [firstPrefix,PCSBCSNativePublicCapture.firstPrefix] at found
  | cons event rest ih =>
    simp only [firstPrefix,PCSBCSNativePublicCapture.firstPrefix] at found ⊢
    split at found
    · rename_i present
      cases found
      simp [PCSBCSNativePublicCapture.firstPrefix,present]
    · rename_i absent
      obtain ⟨earlierEvents,earlier,equal⟩ := Option.map_eq_some_iff.mp found
      subst before
      simp only [List.cons_append,PCSBCSNativePublicCapture.firstPrefix,absent,↓reduceIte]
      exact congrArg (Option.map (event :: ·)) (ih earlierEvents earlier)

/-- The prefix excludes the earliest mentioning event and contains no earlier
mention. In particular it is strictly shorter than the trace containing reply. -/
theorem firstPrefix_earliest {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (events before : List (Event B))
    (found : firstPrefix shape iv ref events = some before) :
    ∃ event rest, events = before ++ event :: rest ∧
      ref ∈ addresses shape iv event.1 ∧ firstPrefix shape iv ref before = none := by
  induction events generalizing before with
  | nil => simp [firstPrefix,PCSBCSNativePublicCapture.firstPrefix] at found
  | cons event rest ih =>
    simp only [firstPrefix,PCSBCSNativePublicCapture.firstPrefix] at found
    split at found
    · rename_i member
      cases found
      exact ⟨event,rest,rfl,member,rfl⟩
    · rename_i absent
      obtain ⟨earlierEvents,earlier,equal⟩ := Option.map_eq_some_iff.mp found
      subst before
      obtain ⟨mention,after,source,member,missing⟩ := ih earlierEvents earlier
      refine ⟨mention,after,by simp [source],member,?_⟩
      simp only [firstPrefix,PCSBCSNativePublicCapture.firstPrefix,absent,↓reduceIte]
      change (firstPrefix shape iv ref earlierEvents).map (event :: ·) = none
      rw [missing]; rfl

theorem firstPrefix_before_reply {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (events before : List (Event B))
    (found : firstPrefix shape iv ref events = some before) : before.length < events.length := by
  obtain ⟨event,rest,rfl,_,_⟩ := firstPrefix_earliest shape iv ref events before found
  simp only [List.length_append,List.length_cons]
  omega

/-- Earlier adversarial disclosure wins; otherwise the current key freezes
exactly the prior prefix BEFORE this key receives its answer. No final-log fill. -/
theorem current_reply_prefix {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (prior after : List (Event B)) (event : Event B)
    (member : ref ∈ addresses shape iv event.1) :
    firstPrefix shape iv ref (prior ++ event :: after) =
      some ((firstPrefix shape iv ref prior).getD prior) := by
  induction prior with
  | nil => simp [firstPrefix,PCSBCSNativePublicCapture.firstPrefix,member]
  | cons old prior ih =>
    simp only [List.cons_append,firstPrefix,PCSBCSNativePublicCapture.firstPrefix]
    by_cases present : ref ∈ addresses shape iv old.1
    · simp [present]
    · simp only [present,↓reduceIte]
      change (firstPrefix shape iv ref (prior ++ event :: after)).map (old :: ·) =
        some (((firstPrefix shape iv ref prior).map (old :: ·)).getD (old :: prior))
      rw [ih]
      cases firstPrefix shape iv ref prior <;> rfl

theorem current_capture {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (prior after : List (Event B)) (event : Event B)
    (member : ref ∈ addresses shape iv event.1) :
    capture shape iv ref (prior ++ event :: after) = some
      (freeze (ordinaryLog ((firstPrefix shape iv ref prior).getD prior)) ref.root ref.shape) := by
  rw [capture,current_reply_prefix shape iv ref prior after event member]; rfl

/-- Covers both branches without a selected-prefix premise: an earlier
adversarial mention is strictly earlier, or the whole prior log is frozen. -/
theorem current_reply_strict {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (prior : List (Event B)) :
    ((firstPrefix shape iv ref prior).getD prior).length < prior.length+1 := by
  cases found : firstPrefix shape iv ref prior with
  | none => simp
  | some before =>
    have strict := firstPrefix_before_reply shape iv ref prior before found
    simp only [Option.getD_some]
    omega

theorem current_answer_independent {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (prior after later : List (Event B))
    (key : PublicCompressionCouplingMixed.Key B) (answer other : Digest32)
    (member : ref ∈ addresses shape iv key) :
    capture shape iv ref (prior ++ ⟨key,answer⟩ :: after) =
      capture shape iv ref (prior ++ ⟨key,other⟩ :: later) := by
  rw [current_capture shape iv ref prior after ⟨key,answer⟩ member,
    current_capture shape iv ref prior later ⟨key,other⟩ member]

theorem capture_extension {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (events later : List (Event B)) (frozen : Frozen)
    (found : capture shape iv ref events = some frozen) :
    capture shape iv ref (events ++ later) = some frozen := by
  obtain ⟨before,earlier,equal⟩ := Option.map_eq_some_iff.mp found
  rw [capture,firstPrefix_extension shape iv ref events before later earlier]
  exact congrArg some equal

theorem root0_extension {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (events later : List (Event B)) (frozen : Frozen)
    (found : capture shape iv ref events = some frozen) :
    root0 shape iv ref (events ++ later) = root0 shape iv ref events := by
  simp only [root0,capture_extension shape iv ref events later frozen found,found]

/-- Full physical image extraction precedes the compact suffix operation. -/
theorem freeze_full_image (log : PublicLog) (shape : SpongefishSessionAdapter.Shape)
    (root : Digest32) :
    imageTable (freeze log root (physicalShape shape)).cells =
      PCSBCSMerkleQueryLog.rawRoot0 log root
        (physicalShape shape).height (physicalShape shape).leafWords ∧
    (freeze log root (physicalShape shape)).raw =
      (PCSBCSMerkleQueryLog.rawRoot0 log root
        (physicalShape shape).height (physicalShape shape).leafWords).map
          (fun image => (image.toList.drop ((physicalShape shape).leafWords-shape.lanes)).toArray) :=
  ⟨imageTable_eq_full _ _ _ _ _,compactTable_eq_drop _ _ _ _ _⟩

theorem captured_shape {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (root : Digest32) (events : List (Event B)) (frozen : Frozen)
    (found : capture shape iv (reference shape root) events = some frozen) :
    shape.Valid ∧ frozen.shape = physicalShape shape ∧
    frozen.raw.size = 2^(physicalShape shape).height ∧
    ∀ row ∈ frozen.raw.toList, row.size = shape.lanes := by
  obtain ⟨before,earlier,equal⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨event,_,_,member,_⟩ := firstPrefix_earliest shape iv _ events before earlier
  have recognized : recognize shape iv event.1 = some (reference shape root) := by
    simpa only [addresses,Option.mem_toList] using member
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,valid,_,_⟩ := recognize_sound shape iv _ _ recognized
  subst frozen
  have rectangular := freeze_shape (ordinaryLog before) root (physicalShape shape)
    (occupied_guard shape valid).2.1
  exact ⟨valid,rfl,rectangular⟩

/-- Literal source leaf hashing is on the full zero-prefixed image. -/
theorem leaf_hash_full (hash : MerkleTransport.Primitive) (leafWords : Nat)
    (index : Nat) (row : List K) :
    MerkleTransport.leafNodes hash leafWords [(index,row)] =
      [(index,hash (ByteCodec.wordsBytes
        (List.replicate (leafWords-row.length) 0 ++ row)))] := rfl

/-- When a frozen full image is present, its getter keeps that exact image and
only then drops the leading zero lanes. Quantified over all rows, not a chosen
opening witness or a presumed root-equality certificate. -/
theorem freeze_cell (log : PublicLog) (shape : SpongefishSessionAdapter.Shape)
    (valid : shape.Valid) (root : Digest32) (index : Nat)
    (inside : index < 2^(physicalShape shape).height) (row : List K)
    (width : row.length = shape.lanes)
    (present : (PCSBCSMerkleQueryLog.fromPublic log root (physicalShape shape).height).get
      (MerkleTransport.addressAbove index (physicalShape shape).height []) =
        some (MerkleBinding.leafImage 0 (physicalShape shape).leafWords row)) :
    ∃ cell, (freeze log root (physicalShape shape)).cells[index]? = some cell ∧
      cell.image = (MerkleBinding.leafImage 0 (physicalShape shape).leafWords row).toArray ∧
      cell.compact = row.toArray ∧ cell.available = true ∧ cell.paddingValid = true := by
  let cell := leafCell (physicalShape shape).leafWords shape.lanes
    (MerkleBinding.leafImage 0 (physicalShape shape).leafWords row)
  have admitted := leafCell_admitted (physicalShape shape).leafWords shape.lanes row width
    (occupied_guard shape valid).2.1
  refine ⟨cell,?_,?_,admitted.2.2,admitted.1,admitted.2.1⟩
  · change (sourceCells log root _ _ _)[index]? = some cell
    rw [sourceCells_get _ _ _ _ _ _ inside]
    simp only [cellAt,present]
    rfl
  · have full := MerkleBinding.leafImage_length (0 : K) (physicalShape shape).leafWords row
      (width ▸ (occupied_guard shape valid).2.1)
    simp only [cell,leafCell,full,↓reduceIte]

/-- Public observations reconstruct the actual mixed draw trace, with the
source's first-answer seed cache. No historical packet allocation is used. -/
def publicCapture {B : Nat} {R : Type} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (view : DuplexModeGame.View R) : Option Frozen :=
  capture shape iv ref (PCSBCSNativePublicCapture.mixedTrace B iv [] view.observations)

theorem publicCapture_source {B : Nat} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (iv : Digest32) (ref : Reference)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (program : DuplexModeGame.Program R) (remaining : Nat) (limit : remaining ≤ B)
    (counted : DuplexModeGame.Counts remaining program) :
    let compiled := PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted
    publicCapture (B := B) shape iv ref
        (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro) compiled) =
      capture shape iv ref
        (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro) compiled).2 := by
  dsimp only [publicCapture]
  rw [PCSBCSNativePublicCapture.mixedTrace_actual B seed ro iv [] program remaining limit counted]

theorem capture_provenance {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : Reference) (events : List (Event B)) (frozen : Frozen)
    (found : capture shape iv ref events = some frozen) :
    ∃ before event after, events = before ++ event :: after ∧
      ref ∈ addresses shape iv event.1 ∧ firstPrefix shape iv ref before = none ∧
      frozen = freeze (ordinaryLog before) ref.root ref.shape ∧
      frozen.queryPrefix = ordinaryLog before ∧ before.length < events.length := by
  obtain ⟨before,earlier,equal⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨event,after,source,member,missing⟩ :=
    firstPrefix_earliest shape iv ref events before earlier
  refine ⟨before,event,after,source,member,missing,equal.symm,?_,
    firstPrefix_before_reply shape iv ref events before earlier⟩
  rw [← equal]
  rfl

private theorem fold_ordinary_authentic {B : Nat} (C : PrimitiveOracle)
    (events : List (Event B))
    (correct : ∀ event ∈ events, ∀ input, event.1 = .inl input → event.2 = C input)
    (prior : PublicLog) (auth : AuthenticLog C prior) :
    AuthenticLog C (events.foldl ordinaryStep prior) := by
  induction events generalizing prior with
  | nil => exact auth
  | cons event rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun e member => correct e (List.mem_cons_of_mem _ member))
    intro input answer member
    cases keyEq : event.1 with
    | inl node =>
      simp only [ordinaryStep,keyEq,List.mem_cons] at member
      rcases member with head | old
      · have same := congrArg Prod.fst head
        have value := congrArg Prod.snd head
        change input = node at same
        rw [same]
        exact (value.trans (correct event List.mem_cons_self node keyEq)).symm
      · exact auth input answer old
    | inr key =>
      simp only [ordinaryStep,keyEq] at member
      exact auth input answer member

/-- Prefix authenticity comes from the actual executed mixed oracle, not a
caller-supplied correspondence or a completed final-log hash table. -/
theorem captured_source_authentic {B n : Nat} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (iv : Digest32) (ref : Reference)
    (C : PrimitiveOracle) (ro : RawKey B → Digest32)
    (program : Sampling (PublicCompressionCouplingMixed.Key B) (fun _ => Digest32) R n)
    (frozen : Frozen)
    (found : capture shape iv ref
      (Sampling.execute (PublicCompressionCouplingMixed.oracle C ro) program).2 = some frozen) :
    AuthenticLog C frozen.queryPrefix := by
  obtain ⟨before,earlier,equal⟩ := Option.map_eq_some_iff.mp found
  rw [← equal]
  change AuthenticLog C (ordinaryLog before)
  apply fold_ordinary_authentic C before _ [] (by simp [AuthenticLog])
  intro event member input keyEq
  have present := PCSBCSNativePublicCapture.firstPrefix_subset (addresses shape iv) ref
    (Sampling.execute (PublicCompressionCouplingMixed.oracle C ro) program).2 before
    earlier event member
  have answer := PCSBCSNativePublicCapture.execute_answers
    (PublicCompressionCouplingMixed.oracle C ro) program event present
  simpa [keyEq,PublicCompressionCouplingMixed.oracle] using answer

/-- Actual successful source openings authenticate the full zero-prefixed
images; the frozen getter returns their compact suffixes, or the existing
compression collision/fresh-target event. This does not assume equality of a
frozen root with a separately selected opening tape. The proof and its output
are the very computation in `accepted`, universally quantified. -/
theorem opened_getter_or_bad (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (shape : SpongefishSessionAdapter.Shape)
    (valid : shape.Valid) (root : Digest32) (proof : MerkleTransport.PrunedMerklePaths)
    (queries : List Nat) (output : List MerkleTransport.RawPath)
    (accepted : proof.open (hash C) root (2^(physicalShape shape).height)
      queries shape.lanes (physicalShape shape).leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (MerkleTransport.hashing (hash C)),
      bytes.length < 2^64) :
    (∀ p ∈ output, ∃ row cell,
      row.length = shape.lanes ∧
      p.leafData = MerkleBinding.leafImage 0 (physicalShape shape).leafWords row ∧
      (freeze log root (physicalShape shape)).cells[p.leafIndex]? = some cell ∧
      cell.image = p.leafData.toArray ∧ cell.compact = row.toArray ∧
      cell.available = true ∧ cell.paddingValid = true) ∨
      PublicMerkleBinding.OpenPrimitiveBad C log root output := by
  have refined := MerkleTransport.open_refines _ _ _ _ _ _ _ _ accepted
  have conditions := ((MerkleTransport.open_spec _ _ _ _ _ _ _ _).mp accepted).1
  have facts : ∀ p ∈ output, p.path.length = (physicalShape shape).height ∧
      p.root (hash C) = root := by
    intro p member
    obtain ⟨q,_,_,_,_,_,_,_,depth,rootEq⟩ :=
      MerkleTransport.forall₂_mem_right refined member
    exact ⟨by simpa only [Nat.log2_two_pow] using depth,rootEq⟩
  rcases PCSBCSMerkleQueryLog.opened_rows C log auth root (physicalShape shape).height output
    (fun p member => (facts p member).1) (fun p member => (facts p member).2) bounds with
    present | bad
  · left
    intro p member
    obtain ⟨q,qMember,row,_,width,indexEq,imageEq,_,_,_⟩ :=
      MerkleTransport.forall₂_mem_right refined member
    have inside : p.leafIndex < 2^(physicalShape shape).height := by
      rw [indexEq]
      exact conditions.range q qMember
    have full := present p member
    rw [imageEq] at full
    obtain ⟨cell,lookup,image,compact,available,padding⟩ :=
      freeze_cell log shape valid root p.leafIndex inside row width full
    exact ⟨row,cell,width,imageEq,lookup,by rw [imageEq]; exact image,
      compact,available,padding⟩
  · exact Or.inr bad

/-- The actual Option getter has exactly the first prefix's full-image
extraction followed by occupied-suffix removal; later logs are not consulted. -/
theorem root0_provenance {B : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (root : Digest32) (events : List (Event B)) (table : Array (Array K))
    (found : root0 shape iv (reference shape root) events = some table) :
    ∃ before event after, events = before ++ event :: after ∧
      reference shape root ∈ addresses shape iv event.1 ∧
      firstPrefix shape iv (reference shape root) before = none ∧
      table = (PCSBCSMerkleQueryLog.rawRoot0 (ordinaryLog before) root
        (physicalShape shape).height (physicalShape shape).leafWords).map
          (fun image => (image.toList.drop ((physicalShape shape).leafWords-shape.lanes)).toArray) := by
  obtain ⟨frozen,captured,sameTable⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨before,event,after,source,member,missing,frozenEq,_,_⟩ :=
    capture_provenance shape iv _ events frozen captured
  refine ⟨before,event,after,source,member,missing,?_⟩
  rw [← sameTable,frozenEq]
  exact (freeze_full_image (ordinaryLog before) shape root).2

#print axioms current_reply_strict
#print axioms current_answer_independent
#print axioms root0_provenance
#print axioms publicCapture_source
#print axioms capture_provenance
#print axioms captured_source_authentic
#print axioms opened_getter_or_bad
#print axioms occupied_guard
#print axioms recognize_sound
#print axioms malformed_key_rejected
#print axioms malformed_header_rejected
#print axioms invalid_shape_rejected
#print axioms receive_membership
#print axioms firstPrefix_source
#print axioms firstPrefix_extension
#print axioms firstPrefix_earliest
#print axioms firstPrefix_before_reply
#print axioms current_reply_prefix
#print axioms current_capture
#print axioms capture_extension
#print axioms root0_extension
#print axioms freeze_full_image
#print axioms captured_shape
#print axioms leaf_hash_full
#print axioms freeze_cell
end Whir.SpongefishCurrentPhysicalRootCapture
