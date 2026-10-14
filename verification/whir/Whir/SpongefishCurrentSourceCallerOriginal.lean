import Whir.SpongefishCurrentAbsorbedPrefix
import Whir.SpongefishCurrentCallerGetter
import Whir.AnchoredSourceCaller
import Whir.PCSBCSCallerBinding

/-! Current #607 original-statement parser/preparation, pinned to
75d4562bde1efe296b4e32d2a195fdfc232b3ead. The deployed parser here is raw32:
the bounded raw-key suffix decoder enumerates at most four records. No trusted
saved record, historical record-byte clone, or supplied decoded claims enter it.
The unchanged logical CPU/rec payload interpreter is reused after current byte
transport. Source byte positions, the literal instance prefix and nonceLE8 are
retained by the existing initialized byte-mode compiler.

Scope: deterministic parser and physical *byte replay* transport, not the whole
native caller equation machine. Public layout metadata must describe the actual
caller; ProductionLayout geometry is explicit in the geometry theorem. The
shared payload's range-only offset semantics are unchanged. Current stack.rs
Statement::check additionally enforces alignment (155-157,207,214); this parser
does not prove that native guard join or extend a lower-level range-only API's
acceptance to malformed offsets. Preparation rejects invalid geometry. The
supported tape has individual E192 reads/draws and positive PoW of at most 64 bits.
Nonce transport is parsed, but PoW/equation acceptance is NOT asserted. The
bijective codec hand-port does not prove Rust's malformed-field/poison behavior.
Read/draw replay errors retain their reached cursor; semantic/header/payload
rejection is Option none and does not assert a native failure cursor. Rows and
Aeneas equivalence, and original-capture-to-binding native joins remain outside
this parser slice. -/
namespace Whir.SpongefishCurrentSourceCallerOriginal
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishSessionAdapter SpongefishRecordBindingParser
open WHIRCallerClaims PCSBCSCallerBinding
set_option autoImplicit false
set_option maxRecDepth 10000

deriving instance DecidableEq for WireKind
deriving instance DecidableEq for SourceEvent

abbrev Payload := List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim

/-- No historical Scalar24 nonce is absorbed. Its logical token's unused value
is zero; the actual nonce read/bind remains eight literal little-endian bytes. -/
def shapeCalls : List WHIRCallerShape.EventShape → Option (List Call)
  | [] => some []
  | .absorb n :: rest => if n = 24 then
      (shapeCalls rest).map (.read .scalar :: ·) else none
  | .squeeze n :: rest => if n = 24 then
      (shapeCalls rest).map (.draw .fold :: ·) else none
  | .nonce bits :: rest => if 0 < bits ∧ bits ≤ 64 then
      (shapeCalls rest).map ([.draw .positivePow,.read .nonce] ++ ·) else none

 def preludeShape (layout : CallerLayout) : List WHIRCallerShape.EventShape :=
  AnchoredSourceCaller.reads (rootScalarCount layout-2)

 def payloadShape (layout : CallerLayout) : List WHIRCallerShape.EventShape :=
  (WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout)

 def calls (layout : CallerLayout) (r : Record) : Option (List Call) := do
  let before ← shapeCalls (preludeShape layout)
  let payload ← shapeCalls (payloadShape layout)
  pure (before ++ [.read .scalar,.read .scalar,.read .scalar,.read .root,
    .draw (.anchor (r.shape.logN-1)),.read .scalar] ++ payload ++
    (messages r).map (fun message => .read message.1))

 def scalar (bytes : List Byte) : Option E := do
  let (value,rest) ← scalarCodec.parse bytes
  if rest = [] then some value else none

 def tokens : List WHIRCallerShape.EventShape → List SourceEvent →
    Option (List CallerToken × List SourceEvent)
  | [], events => some ([],events)
  | .absorb n :: shape, .prover .scalar bytes :: events => do
    if n ≠ 24 then none else do
      let value ← scalar bytes
      let (tail,rest) ← tokens shape events
      pure (.sent value :: tail,rest)
  | .squeeze n :: shape, .verifier bytes :: events => do
    if n ≠ 24 then none else do
      let value ← scalar bytes
      let (tail,rest) ← tokens shape events
      pure (.draw value :: tail,rest)
  | .nonce bits :: shape, .verifier challenge :: .prover .nonce bytes :: events => do
    if ¬ (0 < bits ∧ bits ≤ 64) ∨ challenge.length ≠ 32 then none else do
      let (_,after) ← nonceCodec.parse bytes
      if after ≠ [] then none else do
        let (tail,rest) ← tokens shape events
        pure (.nonce bits (fun _ => 0) :: tail,rest)
  | _, _ => none

 def prelude (layout : CallerLayout) (events : List SourceEvent) : Option (List SourceEvent) := do
  let (ts,events) ← tokens (preludeShape layout) events
  let (_,rest) ← AnchoredSourceCaller.prelude layout ts
  if rest = [] then some events else none

/-- Root, point and value are read from source events, not metadata. Equality to
one raw-decoded candidate is checked only after the literal receive fields parse. -/
 def header (r : Record) : List SourceEvent → Option (List SourceEvent)
  | .prover .scalar a :: .prover .scalar b :: .prover .scalar c ::
      .prover .root root :: .verifier point :: .prover .scalar value :: events => do
    let (decodedRoot,rest) ← SpongefishCurrentAnchorHeader.decode r.shape (a ++ b ++ c ++ root)
    if rest ≠ [] ∨ decodedRoot ≠ r.root then none else do
      let (decodedPoint,rest) ← (vectorCodec r.shape.logN).parse point
      if rest ≠ [] ∨ List.ofFn decodedPoint ≠ r.point then none else do
        let decodedValue ← scalar value
        if decodedValue = r.value then some events else none
  | _ => none

 theorem header_source (r : Record) (events after : List SourceEvent)
    (accepted : header r events = some after) :
    ∃ a b c root pointBytes valueBytes, ∃ (point : Fin r.shape.logN → E),
      events = .prover .scalar a :: .prover .scalar b :: .prover .scalar c ::
        .prover .root root :: .verifier pointBytes :: .prover .scalar valueBytes :: after ∧
      SpongefishCurrentAnchorHeader.decode r.shape (a ++ b ++ c ++ root) = some (r.root,[]) ∧
      (vectorCodec r.shape.logN).parse pointBytes = some (point,[]) ∧
      List.ofFn point = r.point ∧ scalar valueBytes = some r.value := by
  unfold header at accepted
  split at accepted
  · rename_i a b c root pointBytes valueBytes tail
    obtain ⟨⟨decodedRoot,rest⟩,rootEq,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    split at accepted
    · contradiction
    · rename_i rootGuards
      have rootFields : rest = [] ∧ decodedRoot = r.root := by
        simpa only [not_or,ne_eq,not_not] using rootGuards
      obtain ⟨⟨point,rest⟩,pointEq,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      dsimp only at accepted
      split at accepted
      · contradiction
      · rename_i pointGuards
        have pointFields : rest = [] ∧ List.ofFn point = r.point := by
          simpa only [not_or,ne_eq,not_not] using pointGuards
        obtain ⟨value,valueEq,accepted⟩ := Option.bind_eq_some_iff.mp accepted
        split at accepted
        · rename_i valueFields
          cases Option.some.inj accepted
          exact ⟨a,b,c,root,pointBytes,valueBytes,point,rfl,
            by simpa only [rootFields.1,rootFields.2] using rootEq,
            by simpa only [pointFields.1] using pointEq,pointFields.2,
            by simpa only [valueFields] using valueEq⟩
        · contradiction
  · contradiction

 def receiveEvents (r : Record) (pointBytes : List Byte) : List SourceEvent :=
  (SpongefishCurrentAnchorHeader.fields r.shape r.root).map
    (fun message => .prover message.1 message.bytes) ++
    [.verifier pointBytes,.prover .scalar (scalarCodec.bytes r.value)]

 theorem header_encoded (r : Record) (valid : r.shape.Valid)
    (point : Fin r.shape.logN → E) (pointEq : List.ofFn point = r.point)
    (after : List SourceEvent) :
    header r (receiveEvents r ((vectorCodec r.shape.logN).bytes point) ++ after) = some after := by
  have encodedHeader := SpongefishCurrentAnchorHeader.decode_encoded r.shape valid r.root []
  simp only [List.append_nil] at encodedHeader
  have headerBytes :
      scalarCodec.bytes AnchoredHeaderCodec.anchorMarker ++
        scalarCodec.bytes (AnchoredHeaderCodec.shapeScalar r.shape) ++
        scalarCodec.bytes (AnchoredHeaderCodec.lanesScalar r.shape) ++ rootCodec.bytes r.root =
      SpongefishCurrentAnchorHeader.bytes r.shape r.root := by
    simp [SpongefishCurrentAnchorHeader.bytes,commitPrefix,constants,scalarsBytes,
      scalarBytes,rawRoot,Codec.bytes,scalarCodec,rootCodec]
  change (do
    let (root,rest) ← SpongefishCurrentAnchorHeader.decode r.shape
      (scalarCodec.bytes AnchoredHeaderCodec.anchorMarker ++
        scalarCodec.bytes (AnchoredHeaderCodec.shapeScalar r.shape) ++
        scalarCodec.bytes (AnchoredHeaderCodec.lanesScalar r.shape) ++ rootCodec.bytes r.root)
    if rest ≠ [] ∨ root ≠ r.root then none else do
      let (point',rest) ← (vectorCodec r.shape.logN).parse ((vectorCodec r.shape.logN).bytes point)
      if rest ≠ [] ∨ List.ofFn point' ≠ r.point then none else do
        let value ← scalar (scalarCodec.bytes r.value)
        if value = r.value then some after else none) = some after
  have pointRead := Codec.parse_append (vectorCodec r.shape.logN) point []
  have valueRead := Codec.parse_append scalarCodec r.value []
  simp only [List.append_nil] at pointRead valueRead
  rw [headerBytes,encodedHeader]
  simp [pointRead,valueRead,pointEq,scalar]

/-- Successful actual receive supplies the very bytes the current parser uses.
The point, root and value are consequences of receive, never input certificates. -/
 theorem header_from_receive (c : Compression) (before received : Cursor)
    (shape : AnchoredHeaderCodec.Shape) (r : Record)
    (accepted : SpongefishCurrentCommitmentReceive.receive c before shape = some (received,r))
    (after : List SourceEvent) :
    ∃ receivedHeader sampled bytes,
      SpongefishCurrentAnchorHeader.readHeader c before shape = some (receivedHeader,r.root) ∧
      squeezeGroup c receivedHeader (.anchor (shape.logN-1)) = .ok (sampled,bytes) ∧
      read c sampled .scalar = some (received,r.value) ∧
      header r (receiveEvents r bytes ++ after) = some after := by
  obtain ⟨shapeEq,_,_,receivedHeader,sampled,bytes,point,readHeader,drawn,encoded,pointEq,readValue⟩ :=
    SpongefishCurrentCommitmentReceive.receive_retains c before received shape r accepted
  have valid := ((SpongefishCurrentAnchorHeader.readHeader_exact
    c before receivedHeader shape r.root).mp readHeader).1
  refine ⟨receivedHeader,sampled,bytes,readHeader,drawn,readValue,?_⟩
  subst shape
  rw [encoded]
  exact header_encoded r valid point pointEq.symm after

 def payload (layout : CallerLayout) (events : List SourceEvent) :
    Option (Payload × List SourceEvent) := do
  let (ts,events) ← tokens (payloadShape layout) events
  let (claims,rest) ← AnchoredSourceCaller.payload layout ts
  if rest = [] then some (claims,events) else none

 def bindingEvents (r : Record) : List SourceEvent :=
  (messages r).map (fun message => .prover message.1 message.bytes)

 def parseEvents (layout : CallerLayout) (r : Record) (events : List SourceEvent) : Option Payload := do
  if r.shape ≠ AnchoredSourceCaller.shape layout then none else do
    let events ← prelude layout events
    let events ← header r events
    let (claims,events) ← payload layout events
    if events = bindingEvents r then some claims else none

 def indexedFamily (claims : Payload) : Fin claims.1.length → RingPCSGame.FamilyClaim :=
  fun j => claims.1[j]

 def prepare (p : ParameterBounds.Profile) (r : Record) (claims : Payload) :
    Option (CallerInput p) := do
  if familyCap : claims.1.length ≤ 2^64 then
    if claimCap : claims.2.size + 2 ≤ 2^64 then do
      let prepared ← OriginalClaimsChecker.prepare (ParameterBounds.config p) r.shape.lanes
        (indexedFamily claims) claims.2 r.point.toArray r.value
      pure ⟨r.shape.lanes,claims.1.length,indexedFamily claims,claims.2,
        r.point.toArray,r.value,prepared,familyCap,claimCap⟩
    else none
  else none

/-- The initialized session records one public instance before any caller
traffic. Reject other event shapes rather than erasing arbitrary events. -/
def callerEvents : List SourceEvent → Option (List SourceEvent)
  | .publicBytes _ :: events => some events
  | _ => none

/-- Semantic data, including raw errors and reached transport, is preserved
before any original-claims preparation. -/
 def finish (p : ParameterBounds.Profile) (layout : CallerLayout) (q : Coordinate) (r : Record)
    (result : Except (SpongefishCurrentMixedModeCompiler.Data ×
      SpongefishCurrentPrimitiveEventCompiler.ReplayError) SpongefishCurrentMixedModeCompiler.Data) :
    Option (CallerInput p) := do
  let data ← match result with | .error _ => none | .ok data => some data
  if (close data.pending).core.history ≠ q.history ∨ data.narg ≠ [] then none else do
    let events ← callerEvents data.events
    let claims ← parseEvents layout r events
    prepare p r claims

 def historyBytes (q : Coordinate) : List Byte :=
  ((SpongefishCurrentAbsorbedPrefix.parse q.history).map
    SpongefishCurrentAbsorbedPrefix.Prefix.bytes).getD []

/-- The exact current instance prefix is caller metadata, not an invented seed.
Non-byte history, nonzero historical statement seeds and non-output terminals
are outside this current ordinary-byte grammar. -/
 def supported (q : Coordinate) (instanceBytes : List Byte) : Bool :=
  match SpongefishCurrentAbsorbedPrefix.parse q.history with
  | none => false
  | some source => !instanceBytes.isEmpty &&
      (match q.terminal with | .output _ => true | _ => false) &&
      decide (source.bytes.take instanceBytes.length = instanceBytes)

 def replay {Q : Nat} (layout : CallerLayout) (q : Coordinate) (r : Record)
    (instanceBytes : List Byte) (observations : List Observation) :
    Option SpongefishCurrentMixedModeCompiler.Result := do
  if supported q instanceBytes = false then none else do
    let tape ← calls layout r
    let initial := SpongefishCurrentInitializedMode.initial q.history.domain instanceBytes
      ((historyBytes q).drop instanceBytes.length) []
    SpongefishCurrentCallerGetter.run (SpongefishCurrentCallerGetter.answer (Q := Q) observations)
      (SpongefishCurrentMixedModeCompiler.replayProgram initial tape)

 def candidate {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (q : Coordinate) (r : Record) (instanceBytes : List Byte) (observations : List Observation) :
    Option (CallerInput p) := do
  let result ← replay (Q := Q) layout q r instanceBytes observations
  finish p layout q r (SpongefishCurrentMixedModeCompiler.eraseResult result)

/-- Keep every bounded candidate, including ambiguity; do not silently select
an unproved unique suffix. This is the complete dependent prepared result. -/
 def original {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout) (iv : Digest32)
    (key : RawKey Q) (instanceBytes : List Byte) (observations : List Observation) :
    List (CallerInput p) :=
  match WHIRHeaderRoots.decodeRaw iv key with
  | none => []
  | some q => (SpongefishCurrentRecordModeCapture.rawRecords
      (AnchoredSourceCaller.shape layout) iv key).filterMap
      (fun r => candidate (Q := Q) p layout q r instanceBytes observations)

 theorem original_length {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (iv : Digest32) (key : RawKey Q) (instanceBytes : List Byte) (observations : List Observation) :
    (original p layout iv key instanceBytes observations).length ≤ 4 := by
  unfold original
  split
  · simp
  · exact (List.length_filterMap_le _ _).trans
      (SpongefishCurrentRecordModeCapture.rawRecords_length _ _ _)

 theorem original_same_view {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (iv : Digest32) (a b : RawKey Q) (instanceA instanceB : List Byte)
    (observationsA observationsB : List Observation) (keys : a = b)
    (instances : instanceA = instanceB) (observed : observationsA = observationsB) :
    original p layout iv a instanceA observationsA = original p layout iv b instanceB observationsB := by
  cases keys; cases instances; cases observed; rfl

 theorem prepare_exact (p : ParameterBounds.Profile) (r : Record) (claims : Payload)
    (input : CallerInput p) (accepted : prepare p r claims = some input) :
    input.lanes = r.shape.lanes ∧ input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value ∧
    ∃ (fc : claims.1.length ≤ 2^64) (cc : claims.2.size + 2 ≤ 2^64)
      (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config p) r.shape.lanes
        claims.1.length (indexedFamily claims) claims.2 r.point.toArray r.value),
      OriginalClaimsChecker.prepare (ParameterBounds.config p) r.shape.lanes (indexedFamily claims)
        claims.2 r.point.toArray r.value = some prepared ∧
      input = ⟨r.shape.lanes,claims.1.length,indexedFamily claims,claims.2,r.point.toArray,
        r.value,prepared,fc,cc⟩ := by
  unfold prepare at accepted
  split at accepted
  next fc =>
    split at accepted
    next cc =>
      obtain ⟨prepared,computed,equal⟩ := Option.bind_eq_some_iff.mp accepted
      cases Option.some.inj equal
      exact ⟨rfl,rfl,rfl,fc,cc,prepared,computed,rfl⟩
    next => cases accepted
  next => cases accepted

 theorem prepare_computed (p : ParameterBounds.Profile) (r : Record) (claims : Payload)
    (input : CallerInput p) (accepted : prepare p r claims = some input) :
    OriginalClaimsChecker.prepare (ParameterBounds.config p) input.lanes input.family input.points
      input.anchorPoint input.anchorValue = some input.prepared := by
  obtain ⟨_,_,_,fc,cc,prepared,computed,rfl⟩ := prepare_exact p r claims input accepted
  exact computed

 theorem payload_geometry (model : WHIRCallerSupport.ProductionLayout)
    (events after : List SourceEvent) (claims : Payload)
    (accepted : payload model.layout events = some (claims,after)) :
    WHIRCallerGeometry.PayloadValid
      (fun i d => WHIRCallerSupport.columnFits model.sources i d = true)
      (fun o d => WHIRCallerSupport.ringFits model.sources o d = true)
      (callerPlacements model.layout) claims := by
  unfold payload at accepted
  obtain ⟨⟨ts,remaining⟩,_,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  obtain ⟨⟨parsed,rest⟩,parsedEq,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact AnchoredSourceCaller.payload_geometry _ _
      (WHIRCallerSupport.columnFits_mono model.sources) (WHIRCallerSupport.ringFits_mono model.sources)
      model.layout model.geometry ts claims rest parsedEq
  · contradiction

 theorem header_rejected (r : Record) (events : List SourceEvent)
    (missing : header r events = none) (layout : CallerLayout) (initial : List SourceEvent)
    (before : prelude layout initial = some events) : parseEvents layout r initial = none := by
  simp [parseEvents,before,missing]

 theorem missing_reply {A : Type} (q : Query) (next : Digest32 → Program A)
    (get : Query → Option Digest32) (missing : get q = none) :
    SpongefishCurrentCallerGetter.run get (.ask q next) = none := by
  simp [SpongefishCurrentCallerGetter.run,missing]

/-- Physical source replay is independent of the public getter. This retains the
entire cursor/error transport of actualReplay before preparation. -/
 def physicalReplay (C : PrimitiveOracle) (iv : Digest32) (layout : CallerLayout)
    (q : Coordinate) (r : Record) (instanceBytes : List Byte) :
    Option (Except (SpongefishCurrentMixedModeCompiler.Data ×
      SpongefishCurrentPrimitiveEventCompiler.ReplayError) SpongefishCurrentMixedModeCompiler.Data) := do
  if supported q instanceBytes = false then none else do
    let tape ← calls layout r
    let actual := SpongefishCurrentObservedSessionEntry.cursor q.history.domain instanceBytes
      ((historyBytes q).drop instanceBytes.length) []
      (absorb (compressionOf C) (init (compressionOf C) iv q.history.domain) instanceBytes)
    pure (SpongefishCurrentMixedModeCompiler.forgetResult
      (SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) actual tape))

 def physicalCandidate (C : PrimitiveOracle) (iv : Digest32) (p : ParameterBounds.Profile)
    (layout : CallerLayout) (q : Coordinate) (r : Record) (instanceBytes : List Byte) :
    Option (CallerInput p) := do
  let result ← physicalReplay C iv layout q r instanceBytes
  finish p layout q r result

/-- Exact successes AND failures, with full byte transport. The hypothesis is
only coverage of actually requested public construction replies, not decoded
caller fields, checker success, or saved-record equality. -/
 theorem candidate_physical {Q : Nat} (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (layout : CallerLayout) (q : Coordinate) (r : Record)
    (instanceBytes : List Byte) (observations : List Observation)
    (observed : ∀ tape, calls layout r = some tape →
      ∀ o ∈ (runReal C iv (SpongefishCurrentMixedModeCompiler.replayProgram
        (SpongefishCurrentInitializedMode.initial q.history.domain instanceBytes
          ((historyBytes q).drop instanceBytes.length) []) tape)).view.observations,
        SpongefishCurrentCallerGetter.answer (Q := Q) observations o.query = some o.answer) :
    candidate (Q := Q) p layout q r instanceBytes observations =
      physicalCandidate C iv p layout q r instanceBytes := by
  unfold candidate replay physicalCandidate physicalReplay
  by_cases invalid : supported q instanceBytes = false
  · simp [invalid]
  · simp only [invalid]
    cases tapeEq : calls layout r with
    | none => rfl
    | some tape =>
      dsimp only [Bind.bind,Option.bind]
      rw [SpongefishCurrentCallerGetter.run_real C iv _ _ (observed tape tapeEq)]
      have transport := SpongefishCurrentMixedModeCompiler.replay_real C iv
        (SpongefishCurrentInitializedMode.initial q.history.domain instanceBytes
          ((historyBytes q).drop instanceBytes.length) [])
        (SpongefishCurrentObservedSessionEntry.cursor q.history.domain instanceBytes
          ((historyBytes q).drop instanceBytes.length) []
          (absorb (compressionOf C) (init (compressionOf C) iv q.history.domain) instanceBytes))
        rfl (session_bridge (compressionOf C) iv q.history.domain instanceBytes)
        (by intro other d found; cases found) tape
      simp [transport]

 def physicalOriginal {Q : Nat} (C : PrimitiveOracle) (p : ParameterBounds.Profile)
    (layout : CallerLayout) (iv : Digest32) (key : RawKey Q) (instanceBytes : List Byte) :
    List (CallerInput p) :=
  match WHIRHeaderRoots.decodeRaw iv key with
  | none => []
  | some q => (SpongefishCurrentRecordModeCapture.rawRecords
      (AnchoredSourceCaller.shape layout) iv key).filterMap
      (fun r => physicalCandidate C iv p layout q r instanceBytes)

/-- The complete prepared result list, not merely decoded fields, transports.
This equality covers unsupported geometry, bad headers, missing transport,
leftovers, failed replay and failed OriginalClaimsChecker preparation. -/
 theorem original_physical {Q : Nat} (C : PrimitiveOracle) (p : ParameterBounds.Profile)
    (layout : CallerLayout) (iv : Digest32) (key : RawKey Q) (instanceBytes : List Byte)
    (observations : List Observation)
    (observed : ∀ q, WHIRHeaderRoots.decodeRaw iv key = some q →
      ∀ r ∈ SpongefishCurrentRecordModeCapture.rawRecords
        (AnchoredSourceCaller.shape layout) iv key,
      ∀ tape, calls layout r = some tape →
      ∀ o ∈ (runReal C iv (SpongefishCurrentMixedModeCompiler.replayProgram
        (SpongefishCurrentInitializedMode.initial q.history.domain instanceBytes
          ((historyBytes q).drop instanceBytes.length) []) tape)).view.observations,
        SpongefishCurrentCallerGetter.answer (Q := Q) observations o.query = some o.answer) :
    original p layout iv key instanceBytes observations =
      physicalOriginal C p layout iv key instanceBytes := by
  unfold original physicalOriginal
  cases decoded : WHIRHeaderRoots.decodeRaw iv key with
  | none => rfl
  | some q =>
    apply List.filterMap_congr
    intro r member
    exact candidate_physical C iv p layout q r instanceBytes observations
      (observed q decoded r member)

 theorem original_getter_congr {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (iv : Digest32) (key : RawKey Q) (instanceBytes : List Byte) (a b : List Observation)
    (agree : ∀ q, SpongefishCurrentCallerGetter.bounded (Q := Q) a q =
      SpongefishCurrentCallerGetter.bounded (Q := Q) b q) :
    original p layout iv key instanceBytes a = original p layout iv key instanceBytes b := by
  have getter : SpongefishCurrentCallerGetter.answer (Q := Q) a =
      SpongefishCurrentCallerGetter.answer (Q := Q) b := by
    funext query
    cases query with
    | primitive => rfl
    | construction q valid => exact agree q
  simp only [original,candidate,replay,getter]

 theorem parseEvents_geometry (model : WHIRCallerSupport.ProductionLayout) (r : Record)
    (events : List SourceEvent) (claims : Payload)
    (accepted : parseEvents model.layout r events = some claims) :
    WHIRCallerGeometry.PayloadValid
      (fun i d => WHIRCallerSupport.columnFits model.sources i d = true)
      (fun o d => WHIRCallerSupport.ringFits model.sources o d = true)
      (callerPlacements model.layout) claims := by
  unfold parseEvents at accepted
  split at accepted
  · contradiction
  · obtain ⟨afterPrelude,_,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨afterHeader,_,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨⟨parsed,remaining⟩,parsedEq,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact payload_geometry model afterHeader remaining claims parsedEq
    · contradiction

 theorem finish_exact (p : ParameterBounds.Profile) (layout : CallerLayout) (q : Coordinate)
    (r : Record)
    (result : Except (SpongefishCurrentMixedModeCompiler.Data ×
      SpongefishCurrentPrimitiveEventCompiler.ReplayError) SpongefishCurrentMixedModeCompiler.Data)
    (input : CallerInput p) (accepted : finish p layout q r result = some input) :
    ∃ data claims, result = .ok data ∧ (close data.pending).core.history = q.history ∧
      data.narg = [] ∧ (∃ instanceBytes events,
        data.events = .publicBytes instanceBytes :: events ∧
        parseEvents layout r events = some claims) ∧
      prepare p r claims = some input := by
  cases result with
  | error error => simp [finish] at accepted
  | ok data =>
    dsimp only [finish,Bind.bind,Option.bind] at accepted
    split at accepted
    · contradiction
    · rename_i guards
      obtain ⟨events,instanceRead,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨claims,parsed,prepared⟩ := Option.bind_eq_some_iff.mp accepted
      have valid : (close data.pending).core.history = q.history ∧ data.narg = [] := by
        simpa only [not_or,ne_eq,not_not] using guards
      have literal : ∃ instanceBytes, data.events = .publicBytes instanceBytes :: events := by
        cases sourceEq : data.events with
        | nil => simp [callerEvents,sourceEq] at instanceRead
        | cons event rest =>
          cases event <;> simp [callerEvents,sourceEq] at instanceRead
          subst events
          exact ⟨_,rfl⟩
      obtain ⟨instanceBytes,literal⟩ := literal
      exact ⟨data,claims,rfl,valid.1,valid.2,⟨instanceBytes,events,literal,parsed⟩,prepared⟩

 theorem candidate_prepared {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (q : Coordinate) (r : Record) (instanceBytes : List Byte) (observations : List Observation)
    (input : CallerInput p)
    (accepted : candidate (Q := Q) p layout q r instanceBytes observations = some input) :
    input.lanes = r.shape.lanes ∧ input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value ∧
    OriginalClaimsChecker.prepare (ParameterBounds.config p) input.lanes input.family input.points
      input.anchorPoint input.anchorValue = some input.prepared := by
  obtain ⟨result,_,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨_,claims,_,_,_,_,prepared⟩ := finish_exact p layout q r _ input accepted
  obtain ⟨lanes,point,value,_,_,_,_,_⟩ := prepare_exact p r claims input prepared
  exact ⟨lanes,point,value,prepare_computed p r claims input prepared⟩

 theorem original_exact {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (iv : Digest32) (key : RawKey Q) (instanceBytes : List Byte) (observations : List Observation)
    (input : CallerInput p) (member : input ∈ original p layout iv key instanceBytes observations) :
    ∃ q r, WHIRHeaderRoots.decodeRaw iv key = some q ∧
      r ∈ SpongefishCurrentRecordModeCapture.rawRecords (AnchoredSourceCaller.shape layout) iv key ∧
      candidate (Q := Q) p layout q r instanceBytes observations = some input ∧
      input.lanes = r.shape.lanes ∧ input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value ∧
      OriginalClaimsChecker.prepare (ParameterBounds.config p) input.lanes input.family input.points
        input.anchorPoint input.anchorValue = some input.prepared := by
  unfold original at member
  cases decoded : WHIRHeaderRoots.decodeRaw iv key with
  | none => simp [decoded] at member
  | some q =>
    rw [decoded] at member
    obtain ⟨r,inRecords,parsed⟩ := List.mem_filterMap.mp member
    exact ⟨q,r,rfl,inRecords,parsed,
      candidate_prepared p layout q r instanceBytes observations input parsed⟩

 theorem wrong_instance_rejected {Q : Nat} (p : ParameterBounds.Profile) (layout : CallerLayout)
    (q : Coordinate) (r : Record) (instanceBytes : List Byte) (observations : List Observation)
    (unsupported : supported q instanceBytes = false) :
    candidate (Q := Q) p layout q r instanceBytes observations = none := by
  simp [candidate,replay,unsupported]

/-- Native receive+binding supplies suffix membership without any record-byte
certificate. Every advertised anchor field is then a literal receive result.
`SpongefishCurrentAcceptedJoin.accepted_original` joins the accepted payload
subrun to `calls`; native equation acceptance is not asserted here. -/
 theorem receive_binding_candidate {Q : Nat} (c : Compression) (iv : Digest32)
    (before received payloadEnd bound : Cursor) (shape : AnchoredHeaderCodec.Shape) (r : Record)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive c before shape = some (received,r))
    (bindingEq : verify c payloadEnd r = some bound) (valid : r.shape.Valid)
    (pending : r.context.pending.length ≤ 64)
    (framed : SpongefishCurrentModeQueries.FrameDomain bound.pending) (block : Nat)
    (blockBound : block < 2^44)
    (work : pathCost (SpongefishCurrentModeQueries.coordinate bound.pending block) ≤ Q) :
    r ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv
      (constructionKey Q iv (SpongefishCurrentModeQueries.coordinate bound.pending block) work) ∧
    r.context = capture before.state ∧ r.point.length = shape.logN ∧
    ∃ header sampled bytes, ∃ (point : Fin shape.logN → E),
      SpongefishCurrentAnchorHeader.readHeader c before shape = some (header,r.root) ∧
      squeezeGroup c header (.anchor (shape.logN-1)) = .ok (sampled,bytes) ∧
      bytes = (vectorCodec shape.logN).bytes point ∧ r.point = List.ofFn point ∧
      read c sampled .scalar = some (received,r.value) := by
  obtain ⟨shapeEq,contextEq,pointLength,header,sampled,bytes,point,readHeader,drawn,encoded,pointEq,readValue⟩ :=
    SpongefishCurrentCommitmentReceive.receive_retains c before received shape r receivedEq
  refine ⟨?_,contextEq,pointLength,header,sampled,bytes,point,?_⟩
  · rw [← shapeEq]
    exact SpongefishCurrentRecordModeCapture.verified_raw_record c payloadEnd bound r bindingEq
      valid pending (by rw [shapeEq]; exact pointLength) block iv framed blockBound work
  · exact ⟨readHeader,drawn,encoded,pointEq,readValue⟩

#print axioms original_length
#print axioms original_same_view
#print axioms prepare_exact
#print axioms prepare_computed
#print axioms payload_geometry
#print axioms header_rejected
#print axioms missing_reply
#print axioms candidate_physical
#print axioms receive_binding_candidate
#print axioms original_physical
#print axioms original_getter_congr
#print axioms parseEvents_geometry
#print axioms finish_exact
#print axioms candidate_prepared
#print axioms original_exact
#print axioms wrong_instance_rejected
#print axioms header_source
#print axioms header_encoded
#print axioms header_from_receive
end Whir.SpongefishCurrentSourceCallerOriginal
