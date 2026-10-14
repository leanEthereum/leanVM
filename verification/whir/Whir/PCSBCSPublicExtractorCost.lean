import Whir.PCSBCSPublicExtractor
import Whir.PCSBCSPublicLogExtractorCost
import Whir.PCSBCSMerkleRootCacheCost
import Whir.PCSBCSSourceCallerOriginalCost

/-! Value-connected accounting for the computed historical public extractor.
The units are immutable physical input access, fixed-width byte comparison,
logical scalar/Nat operations, list/array operations and the existing field
operation model. No bit-complexity claim about arbitrary Nat encodings is made.
Every observation, including failed, garbage, prequery and repeated records, is in the input.
The 49-bit cursor range is expanded into a constant coefficient, not a promise
about arbitrary natural-number encodings. No native CPU, allocator, prover or
compiled-source refinement claim is made. Proof witnesses are erased; no
mathematical packet carrier is enumerated. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Whir.PCSBCSPublicExtractorCost
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame RawOracleCoupling
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSChallengeOracle
open PCSBCSPublicExtractor

abbrev RawEvent (B : Nat) := Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)

/-- Both bounded lists are materialized. The quadratic surcharge also pays the
known `shortList` linked-list getters created by construction/privateKey; it
does not treat those generated functions as constant-time table callbacks.
External raw input keys, like finite digest/block byte readers, are immutable
physical input tables in the unit-primitive-access boundary. -/
def decodeCount {B : Nat} (iv : Digest32) (key : RawKey B) : Option Coordinate × Nat :=
  let decoded := PCSBCSCoordinateCodecCost.decodeExtractedCount iv (expandKey key)
  (decoded.1,decoded.2+8*(key.1.1.val+key.2.1.val)*(key.1.1.val+key.2.1.val+1)+2)

theorem decodeCount_value {B : Nat} (iv : Digest32) (key : RawKey B) :
    (decodeCount iv key).1 = PCSBCSSourceCoordinateDecoder.decode iv key := by
  simp [decodeCount,PCSBCSCoordinateCodecCost.decodeExtractedCount_value,
    PCSBCSSourceCoordinateDecoder.decode]

def rawCodecPolynomial (K : Nat) : Nat :=
  PCSBCSPublicLogExtractorCost.codecReservation K+32*(K+1)*(K+1)

theorem decodeCount_bound {B : Nat} (iv : Digest32) (key : RawKey B) (K : Nat)
    (left : key.1.1.val ≤ K) (right : key.2.1.val ≤ K) :
    (decodeCount iv key).2 ≤ rawCodecPolynomial K := by
  have h := PCSBCSCoordinateCodecCost.decodeExtractedCount_bound iv (expandKey key)
    (K+1) (by simpa [expandKey,expandShort] using (by omega : key.1.1.val ≤ K+1))
    (by simpa [expandKey,expandShort] using (by omega : key.2.1.val ≤ K+1))
  unfold decodeCount rawCodecPolynomial PCSBCSPublicLogExtractorCost.codecReservation
  dsimp only
  have length : key.1.1.val+key.2.1.val ≤ 2*K := by omega
  have square := Nat.mul_le_mul length (Nat.add_le_add_right length 1)
  nlinarith

/-- Successful decoding relates physical key cells to the actual coordinate
path. This avoids pricing a short key at the external oracle budget B. -/
theorem decoded_physical {B : Nat} {iv : Digest32} {key : RawKey B} {q : Coordinate}
    (found : PCSBCSSourceCoordinateDecoder.decode iv key = some q) :
    pathCost q = key.1.1.val := by
  have same := (PCSBCSSourceCoordinateDecoder.decode_iff iv key q).mp found |>.2
  have lengths := congrArg (fun e : Extracted => e.message.length) same
  simpa only [expandKey,expandShort,List.length_ofFn,(modeKey_lengths iv q).1] using lengths.symm

/-- The same executable classifier, with one byte decode and one pending parse.
The dependent packet constructor reads the schedule once; proof derivations do
not execute. Length, take, block guards and materialization are reserved. -/
def recognizeCount (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    Option (Sigma (EnteredPacket.Block (p := p) (Q := B) (iv := iv) (boundary := boundary))) × Nat :=
  match raw with
  | .inl _ => (none,1)
  | .inr key =>
    let decoded := decodeCount iv key
    match found : decoded.1 with
    | none => (none,decoded.2+1)
    | some q =>
      let entry := PCSBCSSourcePrimitiveRootBudget.entry q boundary
      let entryWork := 3*q.history.frames.length+4
      if entryLength : entry.frames.length = boundary then
        let pending := PCSBCSSourceReferenceParserCost.parsePendingKeyCount p entry q
        match parsed : pending.1 with
        | none => (none,decoded.2+entryWork+pending.2+1)
        | some messages =>
          let tailWork := 4*PCSBCSSourceReferenceParserCost.scheduleWork (ParameterBounds.config p)+
            3*messages.length+q.history.frames.length+16
          match terminal : q.terminal with
          | .output block =>
            if bound : block < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
                (messages.length-1)+31)/32 then
              (some (fromDecoded p B iv boundary key q ((decodeCount_value iv key).symm.trans found)
                entry rfl entryLength messages
                ((PCSBCSSourceReferenceParserCost.parsePendingKeyCount_value p entry q).symm.trans parsed)
                block terminal bound),decoded.2+entryWork+pending.2+tailWork)
            else (none,decoded.2+entryWork+pending.2+tailWork)
          | _ => (none,decoded.2+entryWork+pending.2+tailWork)
      else (none,decoded.2+entryWork)

attribute [local simp] decodeCount_value PCSBCSSourceReferenceParserCost.parsePendingKeyCount_value

theorem recognizeCount_sound (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B)
    (position : Sigma (EnteredPacket.Block (p := p) (Q := B) (iv := iv) (boundary := boundary)))
    (found : (recognizeCount p B iv boundary raw).1 = some position) :
    EnteredPacket.encode position = raw := by
  cases raw with
  | inl input => simp [recognizeCount] at found
  | inr key =>
    simp only [recognizeCount] at found
    split at found
    · contradiction
    · split at found
      · split at found
        · contradiction
        · split at found
          · split at found
            · cases found
              exact fromDecoded_encode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            · contradiction
          · contradiction
      · contradiction

theorem recognizeCount_encode (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (packet : EnteredPacket p B iv boundary) (block : EnteredPacket.Block packet) :
    (recognizeCount p B iv boundary (EnteredPacket.encode ⟨packet,block⟩)).1 = some ⟨packet,block⟩ := by
  have decoded := PCSBCSSourceCoordinateDecoder.decode_constructionKey B iv
    (packet.2.2.coordinate block) (packet.2.2.valid block) (packet.2.2.pathBound block)
  have decoded' : (decodeCount iv (packet.2.2.key block)).1 = some (packet.2.2.coordinate block) :=
    (decodeCount_value iv _).trans decoded
  have entryEq := PCSBCSSourceRootAdmission.packet_entry packet block
  have parsed := parsePendingKey_roundtrip p packet.1.val packet.2.messages
    packet.2.2.nonempty packet.2.2.admitted block.val
  have bound : block.val < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
      (packet.2.messages.length-1)+31)/32 := by
    change block.val < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
      (packet.2.2.messages.length-1)+31)/32
    rw [packet.2.2.width_eq]
    exact block.isLt
  have foundPacket : ∃ actual, (recognizeCount p B iv boundary (EnteredPacket.encode ⟨packet,block⟩)).1 = some actual := by
    change ∃ actual, (recognizeCount p B iv boundary (.inr (packet.2.2.key block))).1 = some actual
    simp only [recognizeCount]
    split
    · rename_i missing
      rw [decoded'] at missing
      cases missing
    · rename_i q found
      have same := Option.some.inj (found.symm.trans decoded')
      subst q
      have length : (PCSBCSSourcePrimitiveRootBudget.entry (packet.2.2.coordinate block) boundary).frames.length =
          boundary := by rw [entryEq]; exact packet.1.property
      rw [dite_eq_left length]
      have pending : (PCSBCSSourceReferenceParserCost.parsePendingKeyCount p
          (PCSBCSSourcePrimitiveRootBudget.entry (packet.2.2.coordinate block) boundary)
          (packet.2.2.coordinate block)).1 = some packet.2.messages := by
        rw [entryEq,PCSBCSSourceReferenceParserCost.parsePendingKeyCount_value]
        exact parsed
      split
      · rename_i missing
        rw [pending] at missing
        cases missing
      · rename_i messages present
        have same := Option.some.inj (present.symm.trans pending)
        subst messages
        simp only [SourcePacket.coordinate,WHIRCallerPrefix.outputKeyFrom]
        rw [dite_eq_left bound]
        exact ⟨_,rfl⟩
  obtain ⟨actual,found⟩ := foundPacket
  have same : actual = ⟨packet,block⟩ :=
    EnteredPacket.encode_injective (recognizeCount_sound p B iv boundary _ actual found)
  simpa [same] using found

theorem recognizeCount_value (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    (recognizeCount p B iv boundary raw).1 = recognize p B iv boundary raw := by
  cases found : (recognizeCount p B iv boundary raw).1 with
  | some position =>
    have encoded := recognizeCount_sound p B iv boundary raw position found
    rw [← encoded]
    exact (recognize_encode p B iv boundary position.1 position.2).symm
  | none =>
    cases other : recognize p B iv boundary raw with
    | none => rfl
    | some position =>
      have encoded := recognize_sound p B iv boundary raw position other
      have present := recognizeCount_encode p B iv boundary position.1 position.2
      rw [encoded,found] at present
      contradiction

/-- Saved bytes and phase roles are decoded without reparsing pending bytes. -/
def packetReferencesCount {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32}
    {boundary : Nat} (packet : EnteredPacket p B iv boundary) : List Reference × Nat :=
  let saved := PCSBCSSourceSavedRecordDecoderCost.decodeCount p packet.1.val
  match saved.1 with
  | none => ([],saved.2+1)
  | some record =>
    (if phaseRolesAdmitted (ParameterBounds.config p) packet.2.messages then
      ⟨record.root,initialShape record.shape⟩ :: phaseReferences (ParameterBounds.config p) packet.2.messages
     else [],saved.2+PCSBCSSourceReferenceParserCost.phaseWork (ParameterBounds.config p)
       packet.2.messages+3*record.shape.logBatch+4)

theorem packetReferencesCount_value {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32}
    {boundary : Nat} (packet : EnteredPacket p B iv boundary) :
    (packetReferencesCount packet).1 = packetReferences packet := by
  simp only [packetReferencesCount,packetReferences,PCSBCSSourceSavedRecordDecoderCost.decodeCount_value]
  cases PCSBCSSourceSavedRecordDecoder.decode p packet.1.val with
  | none => rfl
  | some record =>
    dsimp only [Bind.bind,Option.bind,Pure.pure]
    split <;> rfl

def rawReferencesCount (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) : List Reference × Nat :=
  let classified := recognizeCount p B iv boundary raw
  match classified.1 with
  | none => ([],classified.2+1)
  | some position =>
    let refs := packetReferencesCount position.1
    (refs.1,classified.2+refs.2+1)

theorem rawReferencesCount_value (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    (rawReferencesCount p B iv boundary raw).1 = rawReferences p B iv boundary raw := by
  simp only [rawReferencesCount,rawReferences,recognizeCount_value]
  cases recognize p B iv boundary raw <;> simp [packetReferencesCount_value]

/-- Concrete classifier reservation in physical raw-key cells. -/
def referencePolynomial (p : ParameterBounds.Profile) (W K : Nat) : Nat :=
  let P := PCSBCSRecoveredSourceVolume.recoveredFramePolynomial K
  rawCodecPolynomial K+
    PCSBCSSourceReferencePolynomialBound.pendingKeyPolynomial (ParameterBounds.config p) W P+
    PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial (65*K)+
    (P+1)*(98*PCSBCSSourceReferencePolynomialBound.configSize (ParameterBounds.config p)+4106)+
    4*PCSBCSSourceReferenceParserCost.scheduleWork (ParameterBounds.config p)+8*P+256

theorem rawReferencesCount_bound (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) (W K : Nat)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (keyCap : ∀ key, raw = .inr key → key.1.1.val ≤ K ∧ key.2.1.val ≤ K) :
    (rawReferencesCount p B iv boundary raw).2 ≤ referencePolynomial p W K := by
  cases raw with
  | inl input => simp [rawReferencesCount,recognizeCount,referencePolynomial]
  | inr key =>
    obtain ⟨left,right⟩ := keyCap key rfl
    have codec := decodeCount_bound iv key K left right
    unfold rawReferencesCount
    generalize output : recognizeCount p B iv boundary (.inr key) = result
    unfold recognizeCount at output
    dsimp only at output
    split at output
    · cases output
      dsimp only
      dsimp only [referencePolynomial]
      omega
    · rename_i q found
      have decoded := (decodeCount_value iv key).symm.trans found
      obtain ⟨valid,_⟩ := (PCSBCSSourceCoordinateDecoder.decode_iff iv key q).mp decoded
      have physical : pathCost q ≤ K := by rw [decoded_physical decoded]; exact left
      let P := PCSBCSRecoveredSourceVolume.recoveredFramePolynomial K
      have wire : PCSBCSPublicLogParserCost.framesSize q.history.frames ≤ P :=
        PCSBCSRecoveredSourceVolume.coordinate_wire q valid K physical
      have len := (PCSBCSPublicLogParserCost.framesSize_length q.history.frames).trans wire
      have entryCap := (PCSBCSPublicLogParserCost.framesSize_take q.history.frames boundary).trans wire
      have parser := PCSBCSSourceReferencePolynomialBound.parsePendingKeyCount_work p
        (PCSBCSSourcePrimitiveRootBudget.entry q boundary) q W P width entryCap wire
      have bytes := (PCSBCSPublicLogExtractorCost.bodyUnits_take q.history.frames boundary).trans
        (PCSBCSSourceSavedRecordDecoderCost.coordinate_physical q valid K physical)
      split at output
      · split at output
        · cases output
          dsimp only
          unfold referencePolynomial
          dsimp only [P] at *
          omega
        · rename_i messages pending
          have mass := PCSBCSSourceReferencePolynomialBound.parsePendingKeyCount_mass p
            (PCSBCSSourcePrimitiveRootBudget.entry q boundary) q messages pending
          have count := PCSBCSSourceReferencePolynomialBound.pendingMass_length messages
          have phase := PCSBCSSourceReferencePolynomialBound.phaseWork_bound (ParameterBounds.config p) messages
          have phaseCap : PCSBCSSourceReferenceParserCost.phaseWork (ParameterBounds.config p) messages ≤
              (P+1)*(98*PCSBCSSourceReferencePolynomialBound.configSize (ParameterBounds.config p)+4106)+8 := by
            apply phase.trans
            exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
          have savedWork := PCSBCSSourceSavedRecordDecoderCost.decodeCount_bound p
            (PCSBCSSourcePrimitiveRootBudget.entry q boundary)
          have savedCap : (PCSBCSSourceSavedRecordDecoderCost.decodeCount p
              (PCSBCSSourcePrimitiveRootBudget.entry q boundary)).2 ≤
                PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial (65*K) := by
            apply savedWork.trans
            unfold PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial
            change PCSBCSSourceSavedRecordDecoderCost.physicalSize
              (PCSBCSSourcePrimitiveRootBudget.entry q boundary) ≤ 65*K at bytes
            gcongr
          split at output
          · split at output
            · cases output
              dsimp only [packetReferencesCount,fromDecoded,CanonicalPacket.messages]
              cases saved : (PCSBCSSourceSavedRecordDecoderCost.decodeCount p
                  (PCSBCSSourcePrimitiveRootBudget.entry q boundary)).1 with
              | none => dsimp only; unfold referencePolynomial; dsimp only [P] at *; omega
              | some record =>
                have accepted := (PCSBCSSourceSavedRecordDecoderCost.decodeCount_value p _).symm.trans saved
                have shape := (PCSBCSSourceSavedRecordDecoder.decode_sound p _ record accepted).1
                have batch : record.shape.logBatch < 64 := lt_trans shape.1.1 shape.1.2.1
                dsimp only
                unfold referencePolynomial
                dsimp only [P] at *
                omega
            · cases output; dsimp only; unfold referencePolynomial; dsimp only [P] at *; omega
          · cases output; dsimp only; unfold referencePolynomial; dsimp only [P] at *; omega
      · cases output; dsimp only; unfold referencePolynomial; dsimp only [P] at *; omega

/-- Construction-key materialization reserves the existing plan counter twice:
the source's pathCost guard encodes the coordinate, then constructionKey
encodes it again. Both mapped key lists and their length guards are included.
Cursor arithmetic is a word primitive, not an opaque encoder callback. -/
def constructionReservation (q : Coordinate) : Nat :=
  2*8192*(PCSBCSCoordinateCodecCost.bodyUnits q.history.frames+1)+
    40*(PCSBCSCoordinateCodecCost.bodyUnits q.history.frames+2)+16

theorem constructionReservation_covers (iv : Digest32) (q : Coordinate) :
    (PCSBCSCoordinateCodecCost.planCount q).2+
      (PCSBCSCoordinateCodecCost.modeKeyCount iv q).2+8*pathCost q+8 ≤ constructionReservation q := by
  have work := PCSBCSCoordinateCodecCost.planCount_bound q
  have size := PCSBCSCoordinateCodecCost.framesPlan_length q.history.frames
  have length : (PCSBCSCoordinateCodecCost.planCount q).1.length = pathCost q := by
    rw [PCSBCSCoordinateCodecCost.planCount_value]
    rfl
  have physical : pathCost q ≤ PCSBCSCoordinateCodecCost.bodyUnits q.history.frames+2 := by
    simpa only [pathCost,DuplexEncoding.plan,List.length_cons,List.length_append,List.length_nil]
      using (by omega : (q.history.frames.flatMap DuplexEncoding.framePlan).length+1+1 ≤
        PCSBCSCoordinateCodecCost.bodyUnits q.history.frames+2)
  unfold PCSBCSCoordinateCodecCost.modeKeyCount constructionReservation
  dsimp only
  rw [length]
  omega

def observationDrawCount (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (o : Observation) : List (RawEvent B) × Nat :=
  match o.query with
  | .primitive _ input =>
    let hit := PCSBCSPublicLogExtractorCost.lookupCount log input
    match hit.1 with
    | some _ => ([],1024*hit.2+2)
    | none =>
      let key := PCSBCSPublicLogExtractorCost.privateKeyCount B log input
      (match key.1 with
        | some raw => [⟨.inr raw,o.answer⟩]
        | none => [⟨.inl input,o.answer⟩],1024*hit.2+key.2+4)
  | .construction q _ =>
    if bound : pathCost q ≤ B then
      ([⟨.inr (constructionKey B iv q bound),o.answer⟩],constructionReservation q)
    else ([],constructionReservation q)

theorem observationDrawCount_value (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (o : Observation) :
    (observationDrawCount B iv log o).1 = PCSBCSNativePublicCapture.observationDraw B iv log o := by
  cases o with
  | mk query answer =>
    cases query with
    | primitive purpose input =>
      simp only [observationDrawCount,PCSBCSNativePublicCapture.observationDraw,
        PCSBCSPublicLogExtractorCost.lookupCount_value,PCSBCSPublicLogExtractorCost.privateKeyCount_value]
      cases DuplexPublicSimulator.lookup log input <;> rfl
    | construction q valid => simp only [observationDrawCount,PCSBCSNativePublicCapture.observationDraw]; split <;> rfl

theorem observationDraw_length (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (o : Observation) :
    (PCSBCSNativePublicCapture.observationDraw B iv log o).length ≤ 1 := by
  cases o with
  | mk query answer =>
    cases query with
    | primitive purpose input =>
      simp only [PCSBCSNativePublicCapture.observationDraw]
      split
      · simp
      · split <;> simp
    | construction q valid =>
      simp only [PCSBCSNativePublicCapture.observationDraw]; split <;> simp

def observationPolynomial (Q H : Nat) : Nat :=
  PCSBCSPublicLogExtractorCost.recognitionPolynomial Q+1024*Q+
    2*8192*(H+1)+40*(H+2)+20

theorem observationDrawCount_bound (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (o : Observation) (Q H : Nat)
    (logCap : log.length ≤ Q)
    (historyCap : ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H) :
    (observationDrawCount B iv log o).2 ≤ observationPolynomial Q H := by
  cases o with
  | mk query answer =>
    cases query with
    | primitive purpose input =>
      have scan := PCSBCSPublicLogExtractorCost.findCount_bound
        (fun e : Node × Digest32 => decide (e.1 = input)) log
      change (PCSBCSPublicLogExtractorCost.lookupCount log input).2 ≤ log.length at scan
      have key := (PCSBCSPublicLogExtractorCost.privateKeyCount_bound B log input).trans
        (PCSBCSPublicLogExtractorCost.recognitionPolynomial_mono logCap)
      simp only [observationDrawCount]
      split <;> dsimp only <;> unfold observationPolynomial <;> nlinarith
    | construction q valid =>
      have h := historyCap q valid rfl
      simp only [observationDrawCount]
      split <;> dsimp only <;> unfold constructionReservation observationPolynomial <;> omega

theorem nextLog_length (log : DuplexPublicSimulator.PublicLog) (o : Observation) :
    (PCSBCSNativePublicCapture.nextLog log o).length ≤ log.length+1 := by
  cases o with
  | mk query answer =>
    cases query <;> simp [PCSBCSNativePublicCapture.nextLog,DuplexPublicSimulator.observe]

def mixedTraceCount (B : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog) :
    List Observation → List (RawEvent B) × Nat
  | [] => ([],1)
  | o::rest =>
    let draw := observationDrawCount B iv log o
    let later := mixedTraceCount B iv (PCSBCSNativePublicCapture.nextLog log o) rest
    (draw.1++later.1,draw.2+later.2+draw.1.length+3)

theorem mixedTraceCount_value (B : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (observations : List Observation) :
    (mixedTraceCount B iv log observations).1 = PCSBCSNativePublicCapture.mixedTrace B iv log observations := by
  induction observations generalizing log with
  | nil => rfl
  | cons o rest ih =>
    simp only [mixedTraceCount,PCSBCSNativePublicCapture.mixedTrace,observationDrawCount_value,ih]

theorem mixedTrace_length (B : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (observations : List Observation) :
    (PCSBCSNativePublicCapture.mixedTrace B iv log observations).length ≤ observations.length := by
  induction observations generalizing log with
  | nil => rfl
  | cons o rest ih =>
    have draw := observationDraw_length B iv log o
    have later := ih (PCSBCSNativePublicCapture.nextLog log o)
    simp only [PCSBCSNativePublicCapture.mixedTrace,List.length_append,List.length_cons]
    omega

theorem mixedTraceCount_bound (B : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (observations : List Observation) (Q H : Nat)
    (logCap : log.length+observations.length ≤ Q)
    (historyCap : ∀ o ∈ observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H) :
    (mixedTraceCount B iv log observations).2 ≤
      observations.length*(observationPolynomial Q H+4)+1 := by
  induction observations generalizing log with
  | nil => simp [mixedTraceCount]
  | cons o rest ih =>
    have first := observationDrawCount_bound B iv log o Q H (by simp only [List.length_cons] at logCap; omega)
      (historyCap o (by simp))
    have length := observationDraw_length B iv log o
    rw [← observationDrawCount_value] at length
    have next := nextLog_length log o
    have later := ih (PCSBCSNativePublicCapture.nextLog log o)
      (by simp only [List.length_cons] at logCap; omega)
      (fun item member => historyCap item (List.mem_cons_of_mem o member))
    simp only [mixedTraceCount,List.length_cons]
    nlinarith

theorem rawReferencesCount_size (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    (rawReferencesCount p B iv boundary raw).1.length ≤
      (rawReferencesCount p B iv boundary raw).2 := by
  unfold rawReferencesCount
  dsimp only
  split
  · simp
  · rename_i position present
    unfold packetReferencesCount
    dsimp only
    split
    · simp
    · rename_i record saved
      have phases : (phaseReferences (ParameterBounds.config p) position.1.2.messages).length ≤
          position.1.2.messages.length := by
        unfold phaseReferences
        exact (List.length_filterMap_le _ _).trans (by simp)
      split
      · dsimp only
        simp only [List.length_cons]
        unfold PCSBCSSourceReferenceParserCost.phaseWork
        omega
      · simp

def firstPrefixCount (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) : List (RawEvent B) → Option (List (RawEvent B)) × Nat
  | [] => (none,1)
  | event::rest =>
    let refs := rawReferencesCount p B iv boundary event.1
    let work := refs.2+1024*refs.1.length+2
    if ref ∈ refs.1 then (some [],work) else
      let later := firstPrefixCount p B iv boundary ref rest
      (later.1.map (event::·),work+later.2+1)

theorem firstPrefixCount_value (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (events : List (RawEvent B)) :
    (firstPrefixCount p B iv boundary ref events).1 =
      PCSBCSNativePublicCapture.firstPrefix (rawReferences p B iv boundary) ref events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    simp only [firstPrefixCount,PCSBCSNativePublicCapture.firstPrefix,rawReferencesCount_value]
    split <;> simp [ih]

theorem firstPrefixCount_length (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (events : List (RawEvent B)) :
    ((firstPrefixCount p B iv boundary ref events).1.getD []).length ≤ events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    simp only [firstPrefixCount,List.length_cons]
    split
    · simp
    · cases h : (firstPrefixCount p B iv boundary ref rest).1 <;> simp_all

theorem firstPrefixCount_bound (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (events : List (RawEvent B)) (W K : Nat)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (keys : ∀ event ∈ events, ∀ key, event.1 = .inr key →
      key.1.1.val ≤ K ∧ key.2.1.val ≤ K) :
    (firstPrefixCount p B iv boundary ref events).2 ≤
      events.length*(1025*referencePolynomial p W K+3)+1 := by
  induction events with
  | nil => simp [firstPrefixCount]
  | cons event rest ih =>
    have cost := rawReferencesCount_bound p B iv boundary event.1 W K width (keys event (by simp))
    have size := rawReferencesCount_size p B iv boundary event.1
    have later := ih (fun item member => keys item (List.mem_cons_of_mem event member))
    simp only [firstPrefixCount,List.length_cons]
    split <;> dsimp only <;> nlinarith

def ordinaryLogCount (B : Nat) : PublicMerkleLog.PublicLog → List (RawEvent B) →
    PublicMerkleLog.PublicLog × Nat
  | log,[] => (log,1)
  | log,event::rest =>
    let later := ordinaryLogCount B (PCSBCSNativePublicCapture.rawOrdinary event++log) rest
    (later.1,later.2+2)

theorem ordinaryLogCount_value (B : Nat) (log : PublicMerkleLog.PublicLog) (events : List (RawEvent B)) :
    (ordinaryLogCount B log events).1 = events.foldl
      (fun captured event => PCSBCSNativePublicCapture.rawOrdinary event++captured) log := by
  induction events generalizing log with
  | nil => rfl
  | cons event rest ih => exact ih _

theorem ordinaryLogCount_bound (B : Nat) (log : PublicMerkleLog.PublicLog) (events : List (RawEvent B)) :
    (ordinaryLogCount B log events).2 = 2*events.length+1 ∧
      (ordinaryLogCount B log events).1.length ≤ log.length+events.length := by
  induction events generalizing log with
  | nil => simp [ordinaryLogCount]
  | cons event rest ih =>
    have later := ih (PCSBCSNativePublicCapture.rawOrdinary event++log)
    have first : (PCSBCSNativePublicCapture.rawOrdinary event).length ≤ 1 := by
      unfold PCSBCSNativePublicCapture.rawOrdinary
      split <;> simp
    simp only [ordinaryLogCount,List.length_cons,List.length_append] at *
    constructor <;> omega

def logCount {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) : PublicMerkleLog.PublicLog × Nat :=
  let trace := mixedTraceCount B iv [] view.observations
  let before := firstPrefixCount p B iv boundary ref trace.1
  let captured := ordinaryLogCount B [] (before.1.getD [])
  (captured.1,trace.2+before.2+captured.2+1)

theorem logCount_value {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) :
    (logCount p B iv boundary ref view).1 = log p B iv boundary ref view := by
  simp only [logCount,log,capturedPrefix,mixedTraceCount_value,firstPrefixCount_value,ordinaryLogCount_value]

theorem logCount_length {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) :
    (logCount p B iv boundary ref view).1.length ≤ view.observations.length := by
  have output := (ordinaryLogCount_bound B [] ((firstPrefixCount p B iv boundary ref
    (mixedTraceCount B iv [] view.observations).1).1.getD [])).2
  have before := firstPrefixCount_length p B iv boundary ref (mixedTraceCount B iv [] view.observations).1
  have trace := mixedTrace_length B iv [] view.observations
  rw [← mixedTraceCount_value] at trace
  simp only [List.length_nil,Nat.zero_add] at output
  exact output.trans (before.trans trace)

theorem constructionKey_sizes (B : Nat) (iv : Digest32) (q : Coordinate) (bound : pathCost q ≤ B) :
    (constructionKey B iv q bound).1.1.val = pathCost q ∧
      (constructionKey B iv q bound).2.1.val = pathCost q := by
  have same := expand_constructionKey B iv q bound
  have left := congrArg (fun e : Extracted => e.message.length) same
  have right := congrArg (fun e : Extracted => e.template.length) same
  simpa only [expandKey,expandShort,List.length_ofFn,(modeKey_lengths iv q).1,
    (modeKey_lengths iv q).2] using And.intro left right

theorem pathCost_physical (q : Coordinate) :
    pathCost q ≤ PCSBCSCoordinateCodecCost.bodyUnits q.history.frames+2 := by
  have size := PCSBCSCoordinateCodecCost.framesPlan_length q.history.frames
  simpa only [pathCost,DuplexEncoding.plan,List.length_cons,List.length_append,List.length_nil]
    using (by omega : (q.history.frames.flatMap DuplexEncoding.framePlan).length+1+1 ≤
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames+2)

theorem observationDraw_keys (B : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (o : Observation) (Q H : Nat) (logCap : log.length ≤ Q)
    (historyCap : ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H) :
    ∀ event ∈ PCSBCSNativePublicCapture.observationDraw B iv log o, ∀ key, event.1 = .inr key →
      key.1.1.val ≤ Q+H+2 ∧ key.2.1.val ≤ Q+H+2 := by
  cases o with
  | mk query answer =>
    cases query with
    | primitive purpose input =>
      simp only [PCSBCSNativePublicCapture.observationDraw]
      split
      · simp
      · split
        · rename_i raw found
          have sizes := DuplexPublicSimulator.privateKey_lengths_log found
          intro event member key equal
          simp only [List.mem_singleton] at member
          subst event
          cases equal
          constructor <;> omega
        · intro event member key equal
          simp only [List.mem_singleton] at member
          subst event
          cases equal
    | construction q valid =>
      have volume := historyCap q valid rfl
      have path := pathCost_physical q
      simp only [PCSBCSNativePublicCapture.observationDraw]
      split
      · rename_i bound
        intro event member key equal
        simp only [List.mem_singleton] at member
        subst event
        cases equal
        have sizes := constructionKey_sizes B iv q bound
        constructor <;> omega
      · simp

theorem mixedTrace_keys (B : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (observations : List Observation) (Q H : Nat) (logCap : log.length+observations.length ≤ Q)
    (historyCap : ∀ o ∈ observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H) :
    ∀ event ∈ PCSBCSNativePublicCapture.mixedTrace B iv log observations, ∀ key, event.1 = .inr key →
      key.1.1.val ≤ Q+H+2 ∧ key.2.1.val ≤ Q+H+2 := by
  induction observations generalizing log with
  | nil => simp [PCSBCSNativePublicCapture.mixedTrace]
  | cons o rest ih =>
    have first := observationDraw_keys B iv log o Q H (by simp only [List.length_cons] at logCap; omega)
      (historyCap o (by simp))
    have next := nextLog_length log o
    have later := ih (PCSBCSNativePublicCapture.nextLog log o)
      (by simp only [List.length_cons] at logCap; omega)
      (fun item member => historyCap item (List.mem_cons_of_mem o member))
    intro event member key equal
    rcases List.mem_append.mp member with early | late
    · exact first event early key equal
    · exact later event late key equal

def outerPolynomial (p : ParameterBounds.Profile) (Q H W : Nat) : Nat :=
  Q*(observationPolynomial Q H+1025*referencePolynomial p W (Q+H+2)+9)+4

theorem logCount_bound {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) (Q H W : Nat)
    (observationsCap : view.observations.length ≤ Q)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (historyCap : ∀ o ∈ view.observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H) :
    (logCount p B iv boundary ref view).2 ≤ outerPolynomial p Q H W := by
  have traceWork := mixedTraceCount_bound B iv [] view.observations Q H (by simpa using observationsCap) historyCap
  have traceSize := mixedTrace_length B iv [] view.observations
  have keys := mixedTrace_keys B iv [] view.observations Q H (by simpa using observationsCap) historyCap
  rw [← mixedTraceCount_value] at traceSize keys
  have prefixWork := firstPrefixCount_bound p B iv boundary ref
    (mixedTraceCount B iv [] view.observations).1 W (Q+H+2) width keys
  have prefixSize := firstPrefixCount_length p B iv boundary ref
    (mixedTraceCount B iv [] view.observations).1
  have logWork := (ordinaryLogCount_bound B [] ((firstPrefixCount p B iv boundary ref
    (mixedTraceCount B iv [] view.observations).1).1.getD [])).1
  unfold logCount outerPolynomial
  dsimp only
  nlinarith [Nat.mul_le_mul_right (observationPolynomial Q H+4) observationsCap,
    Nat.mul_le_mul_right (1025*referencePolynomial p W (Q+H+2)+3) (traceSize.trans observationsCap)]

/-- Full literal-coordinate equality is linear in physical history cells.
The two 32-byte headers and fixed terminals are included in the 1024 reserve.
Every observed construction is visited; primitive observations also cost one. -/
def answerStepCount (wanted : Coordinate) (previous : Option Digest32) (o : Observation) :
    Option Digest32 × Nat :=
  (WHIRPhysicalCaller.observeAt wanted previous o,match o.query with
    | .primitive _ _ => 1
    | .construction q _ => 1024+2*PCSBCSCoordinateCodecCost.bodyUnits wanted.history.frames+
        2*PCSBCSCoordinateCodecCost.bodyUnits q.history.frames)

def answerLoopCount (wanted : Coordinate) : Option Digest32 → List Observation → Option Digest32 × Nat
  | previous,[] => (previous,1)
  | previous,o::rest =>
    let first := answerStepCount wanted previous o
    let later := answerLoopCount wanted first.1 rest
    (later.1,first.2+later.2+1)

theorem answerLoopCount_value (wanted : Coordinate) (previous : Option Digest32)
    (observations : List Observation) :
    (answerLoopCount wanted previous observations).1 =
      observations.foldl (WHIRPhysicalCaller.observeAt wanted) previous := by
  induction observations generalizing previous with
  | nil => rfl
  | cons o rest ih => exact ih _

def publicAnswersCount {R : Type} (view : View R) (q : Coordinate) : Digest32 × Nat :=
  let found := answerLoopCount q none view.observations
  (found.1.getD (fun _ => 0),found.2+1)

theorem publicAnswersCount_value {R : Type} (view : View R) (q : Coordinate) :
    (publicAnswersCount view q).1 = PCSBCSNativePublicCapture.publicAnswers view q := by
  simp only [publicAnswersCount,PCSBCSNativePublicCapture.publicAnswers,answerLoopCount_value,
    WHIRPhysicalCaller.latestAnswers,WHIRPhysicalCaller.observedAnswers]

def answerPolynomial (Q J H : Nat) : Nat := Q*(1025+2*J+2*H)+2

theorem answerLoopCount_bound (wanted : Coordinate) (previous : Option Digest32)
    (observations : List Observation) (J H : Nat)
    (wantedCap : PCSBCSCoordinateCodecCost.bodyUnits wanted.history.frames ≤ J)
    (historyCap : ∀ o ∈ observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H) :
    (answerLoopCount wanted previous observations).2 ≤ observations.length*(1025+2*J+2*H)+1 := by
  induction observations generalizing previous with
  | nil => simp [answerLoopCount]
  | cons o rest ih =>
    have step : (answerStepCount wanted previous o).2 ≤ 1024+2*J+2*H := by
      cases o with
      | mk query answer =>
        cases query with
        | primitive purpose input => dsimp only [answerStepCount]; omega
        | construction q valid =>
          have cap := historyCap ⟨.construction q valid,answer⟩ (by simp) q valid rfl
          dsimp only [answerStepCount]
          omega
    have later := ih (answerStepCount wanted previous o).1
      (fun item member => historyCap item (List.mem_cons_of_mem o member))
    simp only [answerLoopCount,List.length_cons]
    nlinarith

theorem publicAnswersCount_bound {R : Type} (view : View R) (entry : FramedHistory)
    (q : Coordinate) (Q J H : Nat) (observationsCap : view.observations.length ≤ Q)
    (entryCap : PCSBCSCoordinateCodecCost.bodyUnits entry.frames ≤ J)
    (member : q ∈ WHIRCallerOutputs.callerOutputs entry)
    (historyCap : ∀ o ∈ view.observations, ∀ coordinate valid, o.query = .construction coordinate valid →
      PCSBCSCoordinateCodecCost.bodyUnits coordinate.history.frames ≤ H) :
    (publicAnswersCount view q).2 ≤ answerPolynomial Q J H := by
  have prefixEq := (WHIRCallerOutputs.callerOutputs_strict_prefix entry q member).2.2.2
  have wantedCap : PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ J := by
    rw [prefixEq]
    exact (PCSBCSPublicLogExtractorCost.bodyUnits_take entry.frames _).trans entryCap
  have work := answerLoopCount_bound q none view.observations J H wantedCap historyCap
  have weighted := Nat.mul_le_mul_right (1025+2*J+2*H) observationsCap
  unfold publicAnswersCount answerPolynomial
  dsimp only
  omega

def extractAtCount {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (original : PCSBCSCallerBinding.CallerInput p)
    (ref : Reference) (view : View R) (originalAccess : Nat) :
    Option (CausalGame.Witness (ParameterBounds.config p) original.lanes) × Nat :=
  let captured := logCount p B iv boundary ref view
  let frozen := PCSBCSPublicLogExtractorCost.freezeCount captured.1 ref.root ref.shape
  let decoded := PCSRoundByRoundSource.countedRun p original.lanes original.family original.points
    original.anchorPoint original.anchorValue frozen.1.raw
  (decoded.1,captured.2+frozen.2+decoded.2*(original.m+1)*(originalAccess+1))

theorem extractAtCount_value {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (original : PCSBCSCallerBinding.CallerInput p)
    (ref : Reference) (view : View R) (originalAccess : Nat) :
    (extractAtCount p B iv boundary original ref view originalAccess).1 =
      extractAt p B iv boundary original ref view := by
  simp only [extractAtCount,extractAt,root,logCount_value,
    PCSBCSPublicLogExtractorCost.freezeCount_value,PCSRoundByRoundSource.countedRun_value,
    PCSRoundByRoundKnowledge.extract]

def backendPolynomial (p : ParameterBounds.Profile) (Q H N L O W lanes M T originalAccess : Nat) : Nat :=
  outerPolynomial p Q H W+PCSBCSMerkleRootCache.operationBudget Q N L O+
    PCSRoundByRoundSource.resourcePolynomial
      (SupportedCandidateExtraction.blockLength (ParameterBounds.config p))
      (SupportedCandidateExtraction.laneCount (ParameterBounds.config p)) lanes M T*(M+1)*(originalAccess+1)

theorem extractAtCount_bound {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (original : PCSBCSCallerBinding.CallerInput p)
    (ref : Reference) (view : View R) (originalAccess Q H N L O W : Nat)
    (observationsCap : view.observations.length ≤ Q)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (historyCap : ∀ o ∈ view.observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H)
    (rowsCap : 2^ref.shape.height ≤ N) (leafCap : ref.shape.leafWords ≤ L)
    (occupiedCap : ref.shape.occupied ≤ O) (fits : ref.shape.occupied ≤ ref.shape.leafWords) :
    (extractAtCount p B iv boundary original ref view originalAccess).2 ≤
      backendPolynomial p Q H N L O W original.lanes original.m original.points.size originalAccess := by
  have outer := logCount_bound p B iv boundary ref view Q H W observationsCap width historyCap
  have logCap := (logCount_length p B iv boundary ref view).trans observationsCap
  have frozen := PCSBCSPublicLogExtractorCost.freezeCount_bound
    (logCount p B iv boundary ref view).1 ref.root ref.shape Q N L O logCap rowsCap leafCap occupiedCap fits
  have kernel := PCSRoundByRoundSource.countedRun_polynomial_cost p original.lanes original.family original.points
    original.anchorPoint original.anchorValue
    (PCSBCSPublicLogExtractorCost.freezeCount (logCount p B iv boundary ref view).1 ref.root ref.shape).1.raw
  have weighted := Nat.mul_le_mul_right (originalAccess+1) (Nat.mul_le_mul_right (original.m+1) kernel)
  unfold extractAtCount backendPolynomial
  dsimp only
  omega

/-- Each actual byte-answer invocation pays a full latest-answer scan. No
unbounded answer callback is declared constant and no block-cache optimization
is substituted for the computed algorithm. `originalAccess` is an explicit
allowance for non-unit original-data accessors in addition to indexed-list work;
setting it to zero means immutable input-table primitive access, not CPU time. -/
def publicOriginalCount {R : Type} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (answerPrice originalAccess : Nat) : Option (PCSBCSCallerBinding.CallerInput p) × Nat :=
  let decoded := PCSBCSSourceCallerOriginalCost.originalCount p layout saved entry
    (PCSBCSNativePublicCapture.publicAnswers view) getters
  (decoded.1,decoded.2.2*(originalAccess+1)+decoded.2.1*answerPrice+1)

theorem publicOriginalCount_value {R : Type} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (answerPrice originalAccess : Nat) :
    (publicOriginalCount p layout saved entry view getters answerPrice originalAccess).1 =
      PCSBCSNativePublicCapture.publicOriginal p layout saved entry view := by
  simp only [publicOriginalCount,PCSBCSNativePublicCapture.publicOriginal,
    PCSBCSSourceCallerOriginalCost.originalCount_value]

def originalDimensions {R : Type} (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (view : View R) : Nat × Nat :=
  PCSBCSSourceCallerOriginalCost.dimensions layout saved entry (PCSBCSNativePublicCapture.publicAnswers view)

def originalGetterCharge {R : Type} (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts) : Nat :=
  PCSBCSSourceCallerOriginalCost.getterCharge layout saved entry (PCSBCSNativePublicCapture.publicAnswers view) getters

def frontPolynomial (p : ParameterBounds.Profile) (P S M T answerPrice originalAccess getterPrice : Nat) : Nat :=
  (PCSBCSSourceCallerOriginalCost.originalPolynomial p P S M T+getterPrice)*(originalAccess+1)+
    P*P*answerPrice+1

theorem publicOriginalCount_bound {R : Type} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (answerPrice originalAccess P S : Nat)
    (entryCap : PCSBCSPublicLogParserCost.framesSize entry.frames ≤ P)
    (layoutCap : PCSBCSCallerPayloadCost.layoutVolume layout ≤ S)
    (recordCap : PCSBCSCallerPayloadCost.recordPublicSize saved ≤ S) (tokensCap : P*P ≤ S) :
    (publicOriginalCount p layout saved entry view getters answerPrice originalAccess).2 ≤
      frontPolynomial p P S (originalDimensions layout saved entry view).1
        (originalDimensions layout saved entry view).2 answerPrice originalAccess
        (originalGetterCharge layout saved entry view getters) := by
  obtain ⟨calls,work⟩ := PCSBCSSourceCallerOriginalCost.originalCount_bound p layout saved entry
    (PCSBCSNativePublicCapture.publicAnswers view) getters P S entryCap layoutCap recordCap tokensCap
  have weighted := Nat.mul_le_mul_right (originalAccess+1) work
  have answers := Nat.mul_le_mul_right answerPrice calls
  unfold publicOriginalCount frontPolynomial originalDimensions originalGetterCharge
  dsimp only
  omega

def extractCount {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (answerPrice originalAccess : Nat) : Option (Output p) × Nat :=
  let original := publicOriginalCount p layout saved entry view getters answerPrice originalAccess
  match original.1 with
  | none => (none,original.2+1)
  | some input =>
    let witness := extractAtCount p B iv boundary input ref view originalAccess
    (witness.1.map (fun w => ⟨input,w⟩),original.2+witness.2+1)

theorem extractCount_value {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (answerPrice originalAccess : Nat) :
    (extractCount p B iv boundary layout saved entry ref view getters answerPrice originalAccess).1 =
      extract p B iv boundary layout saved entry ref view := by
  simp only [extractCount,PCSBCSPublicExtractor.extract,publicOriginalCount_value]
  cases PCSBCSNativePublicCapture.publicOriginal p layout saved entry view with
  | none => rfl
  | some input =>
    simp only [extractAtCount_value]
    dsimp only [Bind.bind,Option.bind]
    cases extractAt p B iv boundary input ref view <;> rfl

def fullPolynomial (p : ParameterBounds.Profile)
    (Q H J P S N L O W lanes M T originalAccess getterPrice : Nat) : Nat :=
  frontPolynomial p P S M T (answerPolynomial Q J H) originalAccess getterPrice+
    backendPolynomial p Q H N L O W lanes M T originalAccess+1

/-- Full computed algorithm, including caller decode/preparation failures and
all physical observations. Only input volumes, target geometry and explicit
source-accessor prices are hypotheses; there is no knowledge/soundness premise. -/
theorem extractCount_bound {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (originalAccess Q H J P S N L O W : Nat)
    (observationsCap : view.observations.length ≤ Q)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (historyCap : ∀ o ∈ view.observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ H)
    (entryCap : PCSBCSPublicLogParserCost.framesSize entry.frames ≤ P)
    (layoutCap : PCSBCSCallerPayloadCost.layoutVolume layout ≤ S)
    (recordCap : PCSBCSCallerPayloadCost.recordPublicSize saved ≤ S) (tokensCap : P*P ≤ S)
    (rowsCap : 2^ref.shape.height ≤ N) (leafCap : ref.shape.leafWords ≤ L)
    (occupiedCap : ref.shape.occupied ≤ O) (fits : ref.shape.occupied ≤ ref.shape.leafWords) :
    (extractCount p B iv boundary layout saved entry ref view getters
      (answerPolynomial Q J H) originalAccess).2 ≤
      fullPolynomial p Q H J P S N L O W saved.shape.lanes
        (originalDimensions layout saved entry view).1 (originalDimensions layout saved entry view).2
        originalAccess (originalGetterCharge layout saved entry view getters) := by
  have front := publicOriginalCount_bound p layout saved entry view getters
    (answerPolynomial Q J H) originalAccess P S entryCap layoutCap recordCap tokensCap
  unfold extractCount
  dsimp only
  cases present : (publicOriginalCount p layout saved entry view getters
      (answerPolynomial Q J H) originalAccess).1 with
  | none => dsimp only; unfold fullPolynomial; omega
  | some input =>
    have shape := PCSBCSSourceCallerOriginalCost.originalCount_dimensions p layout saved entry
      (PCSBCSNativePublicCapture.publicAnswers view) getters input present
    have backend := extractAtCount_bound p B iv boundary input ref view originalAccess Q H N L O W
      observationsCap width historyCap rowsCap leafCap occupiedCap fits
    have dimensionEq : originalDimensions layout saved entry view = (input.m,input.points.size) := shape.2
    have families := congrArg Prod.fst dimensionEq
    have points := congrArg Prod.snd dimensionEq
    dsimp only at families points
    have backendEq : backendPolynomial p Q H N L O W input.lanes input.m input.points.size originalAccess =
        backendPolynomial p Q H N L O W saved.shape.lanes
          (originalDimensions layout saved entry view).1 (originalDimensions layout saved entry view).2
          originalAccess := by rw [shape.1,← families,← points]
    rw [backendEq] at backend
    dsimp only
    unfold fullPolynomial
    omega

def observationHistorySize (o : Observation) : Nat :=
  match o.query with
  | .primitive _ _ => 0
  | .construction q _ => PCSBCSCoordinateCodecCost.bodyUnits q.history.frames

/-- Literal frame slots and payload bytes, with every repeat represented.
Primitive node inputs are fixed-width and are charged by observation length. -/
def physicalHistorySize (observations : List Observation) : Nat :=
  (observations.map observationHistorySize).sum

theorem physicalHistorySize_cap (observations : List Observation) :
    ∀ o ∈ observations, ∀ q valid, o.query = .construction q valid →
      PCSBCSCoordinateCodecCost.bodyUnits q.history.frames ≤ physicalHistorySize observations := by
  intro o member q valid equal
  have h : observationHistorySize o ≤ physicalHistorySize observations :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨o,member,rfl⟩)
  simpa only [observationHistorySize,equal] using h

def callerFrameReservation (entry : FramedHistory) : Nat :=
  (2^49+1)*PCSBCSCoordinateCodecCost.bodyUnits entry.frames

def callerInputSize (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) : Nat :=
  PCSBCSCallerPayloadCost.layoutVolume layout+PCSBCSCallerPayloadCost.recordPublicSize saved+
    callerFrameReservation entry*callerFrameReservation entry+1

/-- A closed polynomial in literal observation/key/history volume, declared
root rows/leaf words/occupied lanes, reached original family/point data and
explicit callback prices. The fixed profile's Gao degree-seven polynomial is
included, not assumed. Metadata-only dimensions do not replace actual N.
The dependent claims dimensions and getter trace are proof-side input metrics,
not additional decoder executions. -/
def physicalPolynomial {R : Type} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (ref : Reference) (view : View R)
    (getters : PCSBCSCallerPayloadCost.OutputCosts) (originalAccess : Nat) : Nat :=
  fullPolynomial p view.observations.length (physicalHistorySize view.observations)
    (PCSBCSCoordinateCodecCost.bodyUnits entry.frames) (callerFrameReservation entry)
    (callerInputSize layout saved entry) (2^ref.shape.height) ref.shape.leafWords ref.shape.occupied
    (2^49) saved.shape.lanes
    (originalDimensions layout saved entry view).1 (originalDimensions layout saved entry view).2
    originalAccess (originalGetterCharge layout saved entry view getters)

/-- Whole computed public-view algorithm, not the previous public-log
extractor. FrameValid is the input codec's fixed cursor domain (49 bits), not
verifier acceptance; without this domain the actual caller decoder expands
numeric cursors and the separate numeric-volume theorem remains applicable.
Occupied ≤ leafWords is declared target geometry, not authentic availability.
All source CPU/context/root/pending getters retain their explicit prices.
Answers are scanned once per actual byte callback, including missing answers. -/
theorem extractCount_physical_polynomial {R : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (getters : PCSBCSCallerPayloadCost.OutputCosts)
    (originalAccess : Nat) (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (fits : ref.shape.occupied ≤ ref.shape.leafWords) :
    (extractCount p B iv boundary layout saved entry ref view getters
      (answerPolynomial view.observations.length (PCSBCSCoordinateCodecCost.bodyUnits entry.frames)
        (physicalHistorySize view.observations)) originalAccess).1 =
        extract p B iv boundary layout saved entry ref view ∧
    (extractCount p B iv boundary layout saved entry ref view getters
      (answerPolynomial view.observations.length (PCSBCSCoordinateCodecCost.bodyUnits entry.frames)
        (physicalHistorySize view.observations)) originalAccess).2 ≤
      physicalPolynomial p layout saved entry ref view getters originalAccess ∧
    (∀ q ∈ WHIRCallerOutputs.callerOutputs entry,
      (publicAnswersCount view q).1 = PCSBCSNativePublicCapture.publicAnswers view q ∧
      (publicAnswersCount view q).2 ≤
        answerPolynomial view.observations.length (PCSBCSCoordinateCodecCost.bodyUnits entry.frames)
          (physicalHistorySize view.observations)) := by
  have entryCap : PCSBCSPublicLogParserCost.framesSize entry.frames ≤ callerFrameReservation entry :=
    PCSBCSRecoveredSourceVolume.framesSize_valid entry.frames entryValid
  have historyCap := physicalHistorySize_cap view.observations
  refine ⟨extractCount_value p B iv boundary layout saved entry ref view getters _ originalAccess,?_,?_⟩
  · exact extractCount_bound p B iv boundary layout saved entry ref view getters originalAccess
      view.observations.length (physicalHistorySize view.observations)
      (PCSBCSCoordinateCodecCost.bodyUnits entry.frames) (callerFrameReservation entry)
      (callerInputSize layout saved entry) (2^ref.shape.height) ref.shape.leafWords ref.shape.occupied
      (2^49) le_rfl (fun n => Nat.le_of_lt (WHIRHistoryKey.stackWidth_bounded p n))
      historyCap entryCap (by unfold callerInputSize; omega) (by unfold callerInputSize; omega)
      (by unfold callerInputSize; omega) le_rfl le_rfl le_rfl fits
  · intro q member
    exact ⟨publicAnswersCount_value view q,
      publicAnswersCount_bound view entry q view.observations.length
        (PCSBCSCoordinateCodecCost.bodyUnits entry.frames) (physicalHistorySize view.observations)
        le_rfl le_rfl member historyCap⟩

/-- All supported profiles, with an exact whole-algorithm value equation and
a physical-input polynomial; the axiom audit below uses only the standard
three kernel axioms, without any supplied algorithm-cost premise. -/
theorem extract_polynomial_cost {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32) (boundary : Nat)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (ref : Reference) (view : View R)
    (getters : PCSBCSCallerPayloadCost.OutputCosts) (originalAccess : Nat)
    (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (fits : ref.shape.occupied ≤ ref.shape.leafWords) :
    (extractCount p B iv boundary layout saved entry ref view getters
      (answerPolynomial view.observations.length (PCSBCSCoordinateCodecCost.bodyUnits entry.frames)
        (physicalHistorySize view.observations)) originalAccess).1 =
        extract p B iv boundary layout saved entry ref view ∧
    (extractCount p B iv boundary layout saved entry ref view getters
      (answerPolynomial view.observations.length (PCSBCSCoordinateCodecCost.bodyUnits entry.frames)
        (physicalHistorySize view.observations)) originalAccess).2 ≤
      physicalPolynomial p layout saved entry ref view getters originalAccess := by
  have checked := extractCount_physical_polynomial p B iv boundary layout saved entry ref view
    getters originalAccess entryValid fits
  exact ⟨checked.1,checked.2.1⟩

#print axioms recognizeCount_value
#print axioms rawReferencesCount_bound
#print axioms mixedTraceCount_value
#print axioms mixedTraceCount_bound
#print axioms logCount_value
#print axioms publicAnswersCount_value
#print axioms extractCount_value
#print axioms extractCount_physical_polynomial
#print axioms extract_polynomial_cost

end Whir.PCSBCSPublicExtractorCost
