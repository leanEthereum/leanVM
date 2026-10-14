import Whir.PCSBCSNativePublicCapture
import Whir.PCSBCSSourcePrimitiveRootBudget
import Whir.PCSBCSSourceRootAdmission
import Whir.PCSBCSWholeSourceObserver

/-! Executable public raw-key reference classification. The parser checks the
full physical key, public boundary, pending schedule and packet block range.
It does not enumerate the mathematical atomic packet carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSPublicExtractor
open Concrete Protocol FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSChallengeOracle

private theorem parsed_output (p : ParameterBounds.Profile) (entry : FramedHistory)
    (q : FiatShamirGame.Coordinate) (messages : List WHIRHistory.Pending) (block : Nat)
    (parsed : parsePendingKey p entry q = some messages) (terminal : q.terminal = .output block) :
    q = WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
      entry messages block := by
  obtain ⟨_,_,other,same⟩ := parsePendingKey_admitted p entry q messages parsed
  have blocksSame : other = block := by
    have h := congrArg FiatShamirGame.Coordinate.terminal same
    simpa [WHIRCallerPrefix.outputKeyFrom,terminal] using h.symm
  simpa [blocksSame] using same

/-- The proofs are erased. Only the parsed history, schedule index and block are
materialized, rather than any finite enumeration of possible source packets. -/
def fromDecoded (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32) (boundary : Nat)
    (key : RawKey B) (q : FiatShamirGame.Coordinate)
    (decoded : PCSBCSSourceCoordinateDecoder.decode iv key = some q)
    (entry : FramedHistory) (entryEq : entry = PCSBCSSourcePrimitiveRootBudget.entry q boundary)
    (entryLength : entry.frames.length = boundary)
    (messages : List WHIRHistory.Pending) (parsed : parsePendingKey p entry q = some messages)
    (block : Nat) (terminal : q.terminal = .output block)
    (blockBound : block < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
      (messages.length-1)+31)/32) :
    Sigma (EnteredPacket.Block (p := p) (Q := B) (iv := iv) (boundary := boundary)) := by
  have nonempty := (parsePendingKey_admitted p entry q messages parsed).1
  have admitted := (parsePendingKey_admitted p entry q messages parsed).2.1
  have depthBound := WHIRHistory.scheduledAdmissible_depth (ParameterBounds.config p) messages admitted
  have sizePositive : 0 < messages.length := List.length_pos_iff.mpr nonempty
  have indexBound : messages.length-1 < WHIRHistory.depth (ParameterBounds.config p) := by omega
  let coordinate := (WHIRHistory.schedule (ParameterBounds.config p))[messages.length-1]'indexBound
  have positionEq : CausalProbability.position coordinate = messages.length-1 :=
    WHIRHistory.position_schedule_get (ParameterBounds.config p) ⟨messages.length-1,indexBound⟩
  have widthEq : WHIRHistoryKey.stackWidth (ParameterBounds.config p) (messages.length-1) =
      24*PCSBCSRounds.rawWidth coordinate := by
    unfold WHIRHistoryKey.stackWidth
    rw [← positionEq,WHIRHistory.schedule_get_position]
    rfl
  have same := parsed_output p entry q messages block parsed terminal
  have entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f := by
    intro f member
    have valid := (PCSBCSSourceCoordinateDecoder.decode_iff iv key q).mp decoded |>.1
    apply valid.1 f
    rw [entryEq] at member
    exact List.mem_of_mem_take member
  have paths : ∀ b : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth coordinate)),
      pathCost (WHIRCallerPrefix.outputKeyFrom
        (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) entry messages b.val) ≤ B := by
    intro b
    have bound := PCSBCSSourceCoordinateDecoder.decode_pathBound decoded
    rw [same] at bound
    rw [WHIRCallerPrefix.pathCostFrom _ (WHIRHistoryKey.stackWidth_positive p) entry
      (WHIRHistoryKey.scheduled_normal _ _ nonempty admitted) b.val]
    rw [WHIRCallerPrefix.pathCostFrom _ (WHIRHistoryKey.stackWidth_positive p) entry
      (WHIRHistoryKey.scheduled_normal _ _ nonempty admitted) block] at bound
    exact bound
  let source : SourcePacket p B iv entry coordinate :=
    ⟨messages,nonempty,admitted,entryValid,positionEq.symm,paths⟩
  let packet : EnteredPacket p B iv boundary := ⟨⟨entry,entryLength⟩,⟨coordinate,source⟩⟩
  have bounded : block < PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth coordinate) := by
    rw [widthEq] at blockBound
    simpa [PCSBCSChallengeOracle.blocks,Nat.mul_comm] using blockBound
  exact ⟨packet,⟨block,bounded⟩⟩

/-- Decode once; fake output blocks outside the grouped packet cannot disclose
an atomic root even when the remaining pending bytes parse. -/
def recognize (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    Option (Sigma (EnteredPacket.Block (p := p) (Q := B) (iv := iv) (boundary := boundary))) :=
  match raw with
  | .inl _ => none
  | .inr key =>
    match decoded : PCSBCSSourceCoordinateDecoder.decode iv key with
    | none => none
    | some q =>
      let entry := PCSBCSSourcePrimitiveRootBudget.entry q boundary
      if entryLength : entry.frames.length = boundary then
        match parsed : parsePendingKey p entry q with
        | none => none
        | some messages =>
          match terminal : q.terminal with
          | .output block =>
            if bound : block < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
                (messages.length-1)+31)/32 then
              some (fromDecoded p B iv boundary key q decoded entry rfl entryLength
                messages parsed block terminal bound)
            else none
          | _ => none
      else none

section Parsed
variable (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32) (boundary : Nat)
    (key : RawKey B) (q : FiatShamirGame.Coordinate)
    (decoded : PCSBCSSourceCoordinateDecoder.decode iv key = some q)
    (entry : FramedHistory) (entryEq : entry = PCSBCSSourcePrimitiveRootBudget.entry q boundary)
    (entryLength : entry.frames.length = boundary)
    (messages : List WHIRHistory.Pending) (parsed : parsePendingKey p entry q = some messages)
    (block : Nat) (terminal : q.terminal = .output block)
    (blockBound : block < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
      (messages.length-1)+31)/32)
local notation "position" => fromDecoded p B iv boundary key q decoded entry entryEq
  entryLength messages parsed block terminal blockBound

theorem fromDecoded_encode : EnteredPacket.encode position = .inr key := by
  change Sum.inr (position.1.2.2.key position.2) = Sum.inr key
  apply congrArg Sum.inr
  apply PublicCompressionCouplingRecognition.expandKey_injective
  dsimp only [fromDecoded,SourcePacket.key,SourcePacket.coordinate]
  rw [expand_constructionKey,← parsed_output p entry q messages block parsed terminal]
  exact ((PCSBCSSourceCoordinateDecoder.decode_iff iv key q).mp decoded).2.symm
end Parsed

theorem recognize_sound (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B)
    (position : Sigma (EnteredPacket.Block (p := p) (Q := B) (iv := iv) (boundary := boundary)))
    (found : recognize p B iv boundary raw = some position) :
    EnteredPacket.encode position = raw := by
  cases raw with
  | inl input => simp [recognize] at found
  | inr key =>
    simp only [recognize] at found
    split at found
    · contradiction
    ·
      split at found
      · split at found
        · contradiction
        · split at found
          · split at found
            · cases found
              exact fromDecoded_encode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            · contradiction
          · contradiction
      · contradiction

theorem recognize_encode (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (packet : EnteredPacket p B iv boundary)
    (block : EnteredPacket.Block packet) :
    recognize p B iv boundary (EnteredPacket.encode ⟨packet,block⟩) = some ⟨packet,block⟩ := by
  unfold EnteredPacket.Block at block
  unfold CanonicalPacket.coord at block
  have decoded : PCSBCSSourceCoordinateDecoder.decode iv (packet.2.2.key block) =
      some (packet.2.2.coordinate block) :=
    PCSBCSSourceCoordinateDecoder.decode_constructionKey B iv
      (packet.2.2.coordinate block) (packet.2.2.valid block) (packet.2.2.pathBound block)
  have entryEq := PCSBCSSourceRootAdmission.packet_entry packet block
  have parsed := parsePendingKey_roundtrip p packet.1.val packet.2.messages
    packet.2.2.nonempty packet.2.2.admitted block.val
  have blockBound : block.val <
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p) (packet.2.messages.length-1)+31)/32 := by
    change block.val < (WHIRHistoryKey.stackWidth (ParameterBounds.config p)
      (packet.2.2.messages.length-1)+31)/32
    rw [packet.2.2.width_eq]
    exact block.isLt
  have found : ∃ actual, recognize p B iv boundary
      (EnteredPacket.encode ⟨packet,block⟩) = some actual := by
    change ∃ actual, recognize p B iv boundary (.inr (packet.2.2.key block)) = some actual
    simp only [recognize]
    split
    · rename_i missing
      rw [decoded] at missing
      cases missing
    · rename_i coordinate foundCoordinate
      have sameCoordinate := Option.some.inj (foundCoordinate.symm.trans decoded)
      subst coordinate
      have length : (PCSBCSSourcePrimitiveRootBudget.entry
          (packet.2.2.coordinate block) boundary).frames.length = boundary := by
        rw [entryEq]
        exact packet.1.property
      rw [dite_eq_left length]
      have parsed' : parsePendingKey p
          (PCSBCSSourcePrimitiveRootBudget.entry (packet.2.2.coordinate block) boundary)
          (packet.2.2.coordinate block) = some packet.2.messages := by
        rw [entryEq]
        exact parsed
      split
      · rename_i missing
        rw [parsed'] at missing
        cases missing
      · rename_i messages foundMessages
        have sameMessages := Option.some.inj (foundMessages.symm.trans parsed')
        subst messages
        simp only [SourcePacket.coordinate,WHIRCallerPrefix.outputKeyFrom]
        rw [dite_eq_left blockBound]
        exact ⟨_,rfl⟩
  obtain ⟨actual,found⟩ := found
  have equal : actual = ⟨packet,block⟩ :=
    EnteredPacket.encode_injective (recognize_sound p B iv boundary _ actual found)
  simpa [equal] using found

theorem recognize_partition (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    recognize p B iv boundary raw =
      (EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)).recognize raw := by
  cases found : recognize p B iv boundary raw with
  | some position =>
    have encoded := recognize_sound p B iv boundary raw position found
    rw [← encoded]
    exact ((EnteredPacket.partition).recognize_encode position).symm
  | none =>
    cases original : (EnteredPacket.partition (p := p) (Q := B)
        (iv := iv) (boundary := boundary)).recognize raw with
    | none => rfl
    | some position =>
      have encoded := (EnteredPacket.partition).encode_recognize raw position original
      change EnteredPacket.encode position = raw at encoded
      have computed := recognize_encode p B iv boundary position.1 position.2
      rw [encoded,found] at computed
      contradiction

#print axioms fromDecoded_encode
#print axioms recognize_sound
#print axioms recognize_encode
#print axioms recognize_partition

def packetReferences {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
    (packet : EnteredPacket p B iv boundary) : List Reference :=
  ((do
    let saved ← PCSBCSSourceSavedRecordDecoder.decode p packet.1.val
    if phaseRolesAdmitted (ParameterBounds.config p) packet.2.messages then
      pure (⟨saved.root,initialShape saved.shape⟩ ::
        phaseReferences (ParameterBounds.config p) packet.2.messages)
    else none) : Option (List Reference)).getD []

theorem packetReferences_address {p : ParameterBounds.Profile} {B : Nat}
    {iv : Digest32} {boundary : Nat} (packet : EnteredPacket p B iv boundary) :
    packetReferences packet = PCSBCSCapturedSourceTransport.address
      (p := p) (Q := B) (iv := iv) (boundary := boundary) (.inl packet) := by
  unfold PCSBCSCapturedSourceTransport.address
    PCSBCSSourcePrimitiveRootBudget.openingReferencesFromEntry packetReferences
  have pending := parsePendingKey_roundtrip p packet.1.val packet.2.messages
    packet.2.2.nonempty packet.2.2.admitted 0
  cases saved : PCSBCSSourceSavedRecordDecoder.decode p packet.1.val with
  | none => simp [saved]
  | some saved =>
    simp only [saved]
    dsimp only [Bind.bind,Option.bind]
    rw [pending]

def rawReferences (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) : List Reference :=
  match recognize p B iv boundary raw with
  | none => []
  | some position => packetReferences position.1

theorem rawReferences_spec (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (raw : PublicCompressionCouplingMixed.Key B) :
    rawReferences p B iv boundary raw = PCSBCSCapturedSourceTransport.address
      (p := p) (Q := B) (iv := iv) (boundary := boundary)
      (PCSBCSNativePublicCapture.allocatedKey raw) := by
  unfold rawReferences
  cases found : recognize p B iv boundary raw with
  | none =>
    dsimp only
    have original : (EnteredPacket.partition (p := p) (Q := B)
        (iv := iv) (boundary := boundary)).recognize raw = none :=
      (recognize_partition p B iv boundary raw).symm.trans found
    unfold PCSBCSNativePublicCapture.allocatedKey
    split
    · rename_i position present
      have impossible := original.symm.trans present
      cases impossible
    · rfl
  | some position =>
    dsimp only
    have original : (EnteredPacket.partition (p := p) (Q := B)
        (iv := iv) (boundary := boundary)).recognize raw = some position :=
      (recognize_partition p B iv boundary raw).symm.trans found
    unfold PCSBCSNativePublicCapture.allocatedKey
    split
    · rename_i actual present
      have equal := Option.some.inj (present.symm.trans original)
      subst actual
      exact packetReferences_address position.1
    · rename_i missing
      have impossible := original.symm.trans missing
      cases impossible

def capturedPrefix {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) :
    Option (List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32))) :=
  PCSBCSNativePublicCapture.firstPrefix (rawReferences p B iv boundary) ref
    (PCSBCSNativePublicCapture.mixedTrace B iv [] view.observations)

theorem prefix_spec {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) :
    capturedPrefix p B iv boundary ref view =
      PCSBCSNativePublicCapture.publicPrefix
        (p := p) (B := B) (iv := iv) (boundary := boundary)
        PCSBCSCapturedSourceTransport.address ref view := by
  unfold capturedPrefix PCSBCSNativePublicCapture.publicPrefix
  congr 1
  funext raw
  exact rawReferences_spec p B iv boundary raw

def log {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) : PublicMerkleLog.PublicLog :=
  ((capturedPrefix p B iv boundary ref view).getD []).foldl
    (fun captured event => PCSBCSNativePublicCapture.rawOrdinary event ++ captured) []

theorem log_spec {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) :
    log p B iv boundary ref view = PCSBCSNativePublicCapture.publicLog
      (p := p) (B := B) (iv := iv) (boundary := boundary)
      PCSBCSCapturedSourceTransport.address ref view := by
  simp only [log,PCSBCSNativePublicCapture.publicLog,prefix_spec]

def root {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) : CausalGame.BaseOracle :=
  (freeze (log p B iv boundary ref view) ref.root ref.shape).raw

theorem root_spec {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (ref : Reference) (view : View R) :
    root p B iv boundary ref view = PCSBCSNativePublicCapture.publicRoot
      (p := p) (B := B) (iv := iv) (boundary := boundary)
      PCSBCSCapturedSourceTransport.address ref view := by
  simp only [root,PCSBCSNativePublicCapture.publicRoot,log_spec]

def extractAt {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (original : PCSBCSCallerBinding.CallerInput p)
    (ref : Reference) (view : View R) :
    Option (CausalGame.Witness (ParameterBounds.config p) original.lanes) :=
  PCSRoundByRoundKnowledge.extract p original.lanes original.family original.points
    original.anchorPoint original.anchorValue (root p B iv boundary ref view)

abbrev Output (p : ParameterBounds.Profile) :=
  Sigma (fun original : PCSBCSCallerBinding.CallerInput p =>
    CausalGame.Witness (ParameterBounds.config p) original.lanes)

/-- Recover the genuinely observed original statement, reconstruct its first
captured Root0, decode once and return only a word explaining all claims.
No oracle, hidden table, verifier tape, strategy or classical selector is read. -/
def extract {R : Type} (p : ParameterBounds.Profile) (B : Nat) (iv : Digest32)
    (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) : Option (Output p) := do
  let original ← PCSBCSNativePublicCapture.publicOriginal p layout saved entry view
  let witness ← extractAt p B iv boundary original ref view
  pure ⟨original,witness⟩

theorem extractAt_output_explains {R : Type} (p : ParameterBounds.Profile) (B : Nat)
    (iv : Digest32) (boundary : Nat) (original : PCSBCSCallerBinding.CallerInput p)
    (ref : Reference) (view : View R)
    (witness : CausalGame.Witness (ParameterBounds.config p) original.lanes)
    (returned : extractAt p B iv boundary original ref view = some witness) :
    PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) original.lanes
      (root p B iv boundary ref view) original.family original.points
      original.anchorPoint original.anchorValue witness :=
  PCSRoundByRoundKnowledge.extract_output_explains p original.lanes original.family
    original.points original.anchorPoint original.anchorValue _ witness returned

theorem extract_output_explains {R : Type} (p : ParameterBounds.Profile) (B : Nat)
    (iv : Digest32) (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (output : Output p)
    (returned : extract p B iv boundary layout saved entry ref view = some output) :
    PCSBCSNativePublicCapture.publicOriginal p layout saved entry view = some output.1 ∧
    PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) output.1.lanes
      (root p B iv boundary ref view) output.1.family output.1.points
      output.1.anchorPoint output.1.anchorValue output.2 := by
  obtain ⟨original,decoded,result⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨witness,decodedWord,equal⟩ := Option.bind_eq_some_iff.mp result
  have same : (⟨original,witness⟩ : Output p) = output := Option.some.inj equal
  subst output
  exact ⟨decoded,extractAt_output_explains p B iv boundary original ref view witness decodedWord⟩

theorem public_failure_iff_extractAt_none {R : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (original : PCSBCSCallerBinding.CallerInput p)
    (decoded : PCSBCSNativePublicCapture.publicOriginal p layout saved entry view = some original) :
    PCSBCSNativePublicCapture.publicExtractionFailed
      (p := p) (B := B) (iv := iv) (boundary := boundary) layout saved entry ref view ↔
      extractAt p B iv boundary original ref view = none := by
  constructor
  · rintro ⟨other,parsed,failed⟩
    have same := Option.some.inj (parsed.symm.trans decoded)
    subst other
    cases returned : extractAt p B iv boundary original ref view with
    | none => rfl
    | some witness =>
      have explains := extractAt_output_explains p B iv boundary original ref view witness returned
      have returned' := returned
      unfold extractAt at returned'
      rw [root_spec] at returned'
      rw [root_spec] at explains
      exact False.elim (failed ⟨witness,returned',explains⟩)
  · intro absent
    refine ⟨original,decoded,?_⟩
    rintro ⟨witness,returned,_⟩
    rw [← root_spec] at returned
    change extractAt p B iv boundary original ref view = some witness at returned
    rw [absent] at returned
    cases returned

theorem public_failure_iff_extract_none {R : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (ref : Reference) (view : View R) (original : PCSBCSCallerBinding.CallerInput p)
    (decoded : PCSBCSNativePublicCapture.publicOriginal p layout saved entry view = some original) :
    PCSBCSNativePublicCapture.publicExtractionFailed
      (p := p) (B := B) (iv := iv) (boundary := boundary) layout saved entry ref view ↔
      extract p B iv boundary layout saved entry ref view = none := by
  rw [public_failure_iff_extractAt_none p B iv boundary layout saved entry ref view original decoded]
  simp only [extract,decoded]
  dsimp only [Bind.bind,Option.bind,Pure.pure]
  cases extractAt p B iv boundary original ref view <;> simp

#print axioms rawReferences_spec
#print axioms prefix_spec
#print axioms log_spec
#print axioms root_spec
#print axioms extractAt_output_explains
#print axioms extract_output_explains
#print axioms public_failure_iff_extract_none

/-- Failed original decoding is not a knowledge failure: the actual accepted
source separately derives successful original decoding. This flag counts
accepted, parsed originals for which the implemented decoder returns no word. -/
def failureObserver (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry)
    (Q B : Nat) (view : PCSBCSWholeSourceObserver.WholeSourceView cap registry Q) : Bool :=
  match view.result.value with
  | none => false
  | some a =>
    let p := a.input.packet.val.profile
    let entry := RawWHIRKeys.entry registry.context a.input.packet.val
    let boundary := entry.frames.length
    match PCSBCSNativePublicCapture.publicOriginal p
        (registry.packetModel Q a.input.packet).layout a.input.record entry view with
    | none => false
    | some original => (extractAt p B registry.context.iv boundary original
        ⟨a.input.record.root,initialShape a.input.record.shape⟩ view).isNone

theorem failureObserver_true_iff (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry)
    (Q B : Nat) (view : PCSBCSWholeSourceObserver.WholeSourceView cap registry Q) :
    failureObserver cap registry Q B view = true ↔
      PCSBCSWholeSourceObserver.PublicFailure cap registry Q B view := by
  cases accepted : view.result.value with
  | none =>
    simp [failureObserver,PCSBCSWholeSourceObserver.PublicFailure,accepted]
  | some a =>
    simp only [failureObserver,accepted]
    cases decoded : PCSBCSNativePublicCapture.publicOriginal a.input.packet.val.profile
        (registry.packetModel Q a.input.packet).layout a.input.record
        (RawWHIRKeys.entry registry.context a.input.packet.val) view with
    | none =>
      simp [PCSBCSWholeSourceObserver.PublicFailure,
        PCSBCSNativePublicCapture.publicExtractionFailed,accepted,decoded]
    | some original =>
      have equivalent := public_failure_iff_extractAt_none a.input.packet.val.profile B
        registry.context.iv (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length
        (registry.packetModel Q a.input.packet).layout a.input.record
        (RawWHIRKeys.entry registry.context a.input.packet.val)
        ⟨a.input.record.root,initialShape a.input.record.shape⟩ view original decoded
      simp only [PCSBCSWholeSourceObserver.PublicFailure,accepted,Option.some.injEq]
      constructor
      · intro empty
        refine ⟨a,rfl,equivalent.mpr ?_⟩
        cases returned : extractAt a.input.packet.val.profile B registry.context.iv
            (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length original
            ⟨a.input.record.root,initialShape a.input.record.shape⟩ view with
        | none => rfl
        | some witness => simp [returned] at empty
      · rintro ⟨other,equal,failed⟩
        subst other
        have absent := equivalent.mp failed
        rw [absent]
        rfl

theorem failureObserver_eq (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry)
    (Q B : Nat) :
    failureObserver cap registry Q B =
      PCSBCSWholeSourceObserver.failureObserver cap registry Q B := by
  funext view
  apply Bool.eq_iff_iff.mpr
  rw [failureObserver_true_iff]
  simp only [PCSBCSWholeSourceObserver.failureObserver,decide_eq_true_eq]

#print axioms failureObserver_true_iff
#print axioms failureObserver_eq

section Probability
variable {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (cap Q : Nat)
    (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV})
    (attacker : Coins → WHIRSourceChronology.Source cap
      (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (B : Nat)
    (counted : ∀ coins, Counts B (PCSBCSNativePhysicalFreeze.wholeProgram
      cap nativeRegistry.val Q (attacker coins)))
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (sourceClass : ∀ coins, PCSBCSWholeSourceObserver.SourceClass
      cap nativeRegistry.val Q p layout boundary (attacker coins))
    (rootRegistry : AnchoredHeaderRoots.Public)

include counted sourceClass rootRegistry in
/-- The event is failure of this implemented public-view extractor, not a
caller-supplied failure certificate. This is the historical PCS-only ideal
compression experiment and its explicit aggregate source-work loss. -/
theorem random_compression_failure_probability (familyCap : cap ≤ 2^64) :
    realProbability nativeRegistry.val.context.iv
      (fun coins => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q (attacker coins))
      (failureObserver cap nativeRegistry.val Q B) ≤
        (B : ℚ)*((17/32 : ℚ)^56 + 1/2^78) +
        min 1 ((2*(B : ℚ)^2-(B : ℚ))/2^256) +
        ((B : ℚ)^3+3*(B : ℚ)^2-2*(B : ℚ))/2^256 := by
  rw [failureObserver_eq]
  exact PCSBCSWholeSourceObserver.explicit_failure_probability cap Q nativeRegistry
    attacker B counted p layout boundary sourceClass rootRegistry familyCap
end Probability

#print axioms random_compression_failure_probability

end Whir.PCSBCSPublicExtractor
