import Whir.SpongefishCurrentCommitmentReceive
import Whir.SpongefishCurrentRecordOpeningQueries
import Whir.SpongefishCurrentPhysicalRootCapture
import Whir.SpongefishCurrentPrimitiveEventCompiler
import Whir.SpongefishCurrentInitializedMode
import Whir.SpongefishCurrentRoundSeparation
import Whir.SpongefishCurrentObservedRecordBinding

/-! Real BLAKE2s execution of the current byte-adapter paths, including raw-root
mismatch, truncated immutable record and an output-block boundary. This is a
hand-port regression, not a Rust compiler or whole native acceptance theorem. -/
open Whir Whir.Concrete Whir.FiatShamirGame Whir.DuplexRefinement Whir.DuplexFraming
open Whir.SpongefishSessionAdapter Whir.SpongefishPCSRoundFrames

private def report (label : String) : IO Unit := do
  IO.println s!"current adapter: {label}"
  (← IO.getStdout).flush

private def eventBytes (events : List SourceEvent) : List Byte :=
  events.flatMap fun event => match event with
    | .publicBytes bytes | .prover _ bytes | .verifier bytes | .hint bytes => bytes

def main : IO Unit := do
  let C := DuplexModeGame.blake2sOracle
  let c := DuplexModeGame.compressionOf C
  let parameter := DuplexCompression.parameterIV
  let tag := ([] : List Byte)
  let derived := DuplexModeGame.runReal C parameter (SpongefishOrdinarySession.deriveProgram parameter tag)
  let session := derived.view.result
  unless withDerived c parameter tag (fun expected =>
      Array.ofFn expected = Array.ofFn session) && derived.view.observations.length = 2 do
    throw (IO.userError "observed session derivation disagrees")
  report "observed session derivation agrees"
  let instanceBytes : List Byte := [11]
  let valueBytes := scalarBytes (E.ofK 9)
  let initializedNarg := rawRoot zeroDigest ++ valueBytes
  let initializedCalls : List Call :=
    [.read .root,.draw .fold,.draw .fold,.read .scalar,.draw .fold,.hint]
  let initialized := DuplexModeGame.runReal C parameter
    (SpongefishCurrentInitializedMode.program parameter tag instanceBytes initializedNarg [[7]] initializedCalls)
  let some (.ok initializedData) := initialized.view.result
    | throw (IO.userError "observed initialized mixed entry rejected valid input")
  let some (.ok actualInitialized) :=
    SpongefishCurrentObservedSessionEntry.actualEntry c parameter tag instanceBytes initializedNarg [[7]] initializedCalls
    | throw (IO.userError "actual initialized replay rejected valid input")
  unless initializedData.narg = [] && initializedData.bytesRead = 56 &&
      initializedData.messagesRead = 2 && initializedData.hintsRead = 1 &&
      initializedData.pending.frames = actualInitialized.pending.frames &&
      initializedData.pending.consumed = actualInitialized.pending.consumed &&
      eventBytes initializedData.events = eventBytes actualInitialized.events do
    throw (IO.userError "initialized mixed replay disagrees on actual bytes, cache reuse or reached state")
  let ordinaryCount := initialized.view.observations.countP fun o => match o.query with
    | .primitive _ _ => true | .construction _ _ => false
  let constructionCount := initialized.view.observations.countP fun o => match o.query with
    | .primitive _ _ => false | .construction _ _ => true
  unless ordinaryCount = 3 && constructionCount = 3 &&
      initialized.primitiveCost ≤ SpongefishCurrentInitializedMode.budget tag instanceBytes initializedCalls do
    throw (IO.userError "session seed or full-coordinate cache work disagrees")
  report "observed initialized session and mixed replay matched actual bytes across shared and fresh output blocks"
  let rejectedEntry := DuplexModeGame.runReal C parameter
    (SpongefishCurrentInitializedMode.program parameter tag instanceBytes
      (rawRoot zeroDigest ++ valueBytes.take 23) [[7]] initializedCalls)
  let some (.error (rejectedData,.readRejected .scalar)) := rejectedEntry.view.result
    | throw (IO.userError "initialized mode did not retain scalar rejection")
  unless rejectedData.bytesRead = 32 && rejectedData.messagesRead = 1 &&
      rejectedData.narg.length = 23 && rejectedData.pending.consumed = 48 &&
      rejectedData.hintsRead = 0 do
    throw (IO.userError "initialized mode charged or mutated an unreached rejected suffix")
  report "observed initialized mode retained reached reject prefix and no later hint"
  let observedShape : Shape := ⟨2,1,1,1⟩
  let receiveBytes := SpongefishCurrentAnchorHeader.bytes observedShape zeroDigest ++ valueBytes
  let some observedStart := SpongefishCurrentObservedSessionEntry.actualSetup c parameter tag
      instanceBytes receiveBytes []
    | throw (IO.userError "observed-record constructor rejected")
  let some (_,observedRecord) := SpongefishCurrentCommitmentReceive.receive c observedStart observedShape
    | throw (IO.userError "observed-record literal receive rejected")
  let expectedBytes := (SpongefishRecordBindingParser.messages observedRecord).flatMap
    (fun message => message.bytes)
  let observedInput := receiveBytes ++ expectedBytes
  let observedRun := DuplexModeGame.runReal C parameter
    (SpongefishCurrentObservedRecordBinding.program parameter tag instanceBytes observedInput []
      observedShape [] [])
  let some (.ok (observedSnapshot,retainedRecord)) := observedRun.view.result
    | throw (IO.userError "observed initialized record composition rejected")
  unless observedSnapshot.1.narg = [] && observedSnapshot.1.bytesRead = observedInput.length &&
      retainedRecord.point = observedRecord.point && retainedRecord.value = observedRecord.value &&
      Array.ofFn retainedRecord.context.cv = Array.ofFn (capture observedStart.state).cv &&
      retainedRecord.context.pending = (capture observedStart.state).pending &&
      retainedRecord.context.previous = (capture observedStart.state).previous &&
      retainedRecord.context.squeezed = (capture observedStart.state).squeezed do
    throw (IO.userError "observed record did not retain its computed pre-header context")
  report "observed initialized receive and expected-record binding derived the actual immutable context"
  let foreignRecord := {observedRecord with root := fun _ => 1}
  let foreignBytes := (SpongefishRecordBindingParser.messages foreignRecord).flatMap
    (fun message => message.bytes)
  let foreignRun := DuplexModeGame.runReal C parameter
    (SpongefishCurrentObservedRecordBinding.program parameter tag instanceBytes
      (receiveBytes ++ foreignBytes) [] observedShape [] [])
  let some (.error (foreignSnapshot,.fieldMismatch .root)) := foreignRun.view.result
    | throw (IO.userError "foreign expected-record root was not rejected after its read")
  unless foreignSnapshot.1.bytesRead = receiveBytes.length + 104 &&
      foreignSnapshot.1.narg.length = foreignBytes.length - 104 do
    throw (IO.userError "foreign record rejection lost the reached post-absorb cursor")
  report "observed opening mismatch retained read-first-compare-second rejection transport"
  let layout : OpeningLayout :=
    ⟨2,⟨2,1,3,5,⟨1,by decide⟩⟩,[(1,⟨1,1,2,3,⟨0,by decide⟩⟩)],1,2,1,3,⟨0,by decide⟩⟩
  unless SpongefishCurrentRoundSeparation.scan false layout.schedule = some true &&
      (SpongefishCurrentRoundSeparation.scan false [.draw .fold,.hint,.draw .fold]).isNone do
    throw (IO.userError "current round separation accepted a hint as an absorbed prover payload")
  report "actual current PCS schedule separated verifier messages; a transport hint alone did not"
  let state := init c parameter session
  let pending : Pending := {domain := session}
  let shape : Shape := ⟨2,1,1,1⟩
  let header := SpongefishCurrentAnchorHeader.bytes shape zeroDigest
  let headerCursor : Cursor := {state,pending,narg := header ++ [7]}
  let (headerAfter,headerRoot) ← match SpongefishCurrentAnchorHeader.readHeader c headerCursor shape with
    | some result => pure result
    | none => throw (IO.userError "canonical raw32 preanchor header rejected")
  unless headerAfter.narg = [7] && headerAfter.bytesRead = 104 &&
      headerAfter.messagesRead = 4 && Array.ofFn headerRoot = Array.ofFn zeroDigest do
    throw (IO.userError "preanchor header root or exact cursor differs")
  let headerQuery := SpongefishCurrentModeQueries.coordinate headerAfter.pending 0
  if bounded : pathCost headerQuery ≤ 4096 then
    let raw := DuplexModeGame.constructionKey 4096 parameter headerQuery bounded
    unless (SpongefishCurrentAnchorHeader.rawHeader shape parameter raw).map Array.ofFn =
        some (Array.ofFn zeroDigest) do
      throw (IO.userError "raw preanchor coordinate lost its root")
    let ref := SpongefishCurrentPhysicalRootCapture.reference shape zeroDigest
    let key : PublicCompressionCouplingMixed.Key 4096 := .inr raw
    let input : DuplexFraming.Node := ⟨zeroDigest,fun _ => 0,0,true⟩
    let prior : List (SpongefishCurrentPhysicalRootCapture.Event 4096) :=
      [⟨.inl input,C input⟩]
    let events := prior ++ [⟨key,zeroDigest⟩]
    let some frozen := SpongefishCurrentPhysicalRootCapture.capture shape parameter ref events
      | throw (IO.userError "current literal raw key did not capture the physical root")
    unless frozen.queryPrefix = [(input,C input)] do
      throw (IO.userError "current root capture included its own answer or lost the strict prefix")
    let extended := events ++ [⟨key,fun i => if i.val = 0 then 1 else 0⟩]
    let some retained := SpongefishCurrentPhysicalRootCapture.capture shape parameter ref extended
      | throw (IO.userError "earlier adversarial root mention was lost")
    unless retained.raw = frozen.raw && retained.queryPrefix = frozen.queryPrefix do
      throw (IO.userError "later current reply replaced the first physical root capture")
    report "literal current physical root reused its earliest strict prefix independently of later replies"
  else
    throw (IO.userError "preanchor header exceeded the smoke query budget")
  let anchorBytes ← match DuplexRefinement.squeeze c headerAfter.state (24*shape.logN) with
    | .ok (_,bytes) => pure bytes
    | .error _ => throw (IO.userError "preanchor point squeeze failed")
  unless anchorBytes.length = 48 do
    throw (IO.userError "preanchor point squeeze returned the wrong byte count")
  unless (SpongefishCurrentAnchorHeader.readHeader c
      {headerCursor with narg := header.take 103} shape).isNone do
    throw (IO.userError "truncated preanchor header accepted")
  report "raw32 preanchor header and literal root captured before 48 point bytes; truncation rejected"
  let value := E.ofK 9
  let transport := header ++ scalarCodec.bytes value ++ [7]
  let receiveCursor : Cursor := {state,pending,narg := transport}
  let (receivedAfter,received) ← match SpongefishCurrentCommitmentReceive.receive c receiveCursor shape with
    | some result => pure result
    | none => throw (IO.userError "actual commitment-receive operation rejected canonical input")
  let some (sampledPoint,pointRest) := (vectorCodec shape.logN).parse anchorBytes
    | throw (IO.userError "actual sampled point failed its canonical codec")
  unless pointRest = [] && received.point = List.ofFn sampledPoint &&
      received.value = value && Array.ofFn received.root = Array.ofFn zeroDigest &&
      receivedAfter.narg = [7] && receivedAfter.bytesRead = 128 &&
      receivedAfter.messagesRead = 5 do
    throw (IO.userError "actual receive point, root, value or individual cursor differs")
  unless (SpongefishCurrentCommitmentReceive.receive c
      {receiveCursor with narg := transport.take 127} shape).isNone do
    throw (IO.userError "truncated actual anchor value accepted")
  report "actual commitment receive retained sampled point, raw root and later prover value; truncated value rejected"
  let calls : List Call := [.read .scalar,.read .scalar,.read .scalar,.read .root,
    .draw (.anchor (shape.logN-1)),.read .scalar]
  let compiled := DuplexModeGame.runReal C parameter
    (SpongefishCurrentPrimitiveEventCompiler.replayProgram receiveCursor calls)
  let compiledAfter ← match compiled.view.result with
    | .ok result => pure result
    | .error _ => throw (IO.userError "observed current primitive compiler rejected canonical receive")
  unless compiledAfter.narg = receivedAfter.narg &&
      compiledAfter.bytesRead = receivedAfter.bytesRead &&
      compiledAfter.messagesRead = receivedAfter.messagesRead &&
      compiledAfter.state.pending = receivedAfter.state.pending &&
      compiledAfter.state.consumed = receivedAfter.state.consumed &&
      Array.ofFn compiledAfter.state.cv = Array.ofFn receivedAfter.state.cv do
    throw (IO.userError "observed current compiler differs from actual receive")
  let rejecting := DuplexModeGame.runReal C parameter
    (SpongefishCurrentPrimitiveEventCompiler.replayProgram
      {receiveCursor with narg := transport.take 127} calls)
  match rejecting.view.result with
  | .error (reached,.readRejected .scalar) =>
    unless reached.bytesRead = 104 && reached.messagesRead = 4 &&
        reached.state.consumed = 48 do
      throw (IO.userError "rejecting current compiler lost the reached pre-value cursor")
  | _ => throw (IO.userError "current compiler did not report the truncated later value")
  report "observed primitive compiler matched actual receive and retained rejecting-prefix state"
  let record : Record := {
    shape := ⟨2,1,1,1⟩,root := zeroDigest,
    context := ⟨zeroDigest,[1,2,3,4,5],true,0,0⟩,
    point := [0,0],value := 0 }
  let source := openingBytes record
  let cur : Cursor := {state,pending,narg := source ++ [9,10]}
  let after ← match SpongefishRecordBindingParser.verify c cur record with
    | some next => pure next
    | none => throw (IO.userError "canonical current record rejected")
  unless after.narg = [9,10] && after.bytesRead = source.length &&
      after.messagesRead = (SpongefishRecordBindingParser.messages record).length do
    throw (IO.userError "source record cursor or individual reads disagree")
  report "raw-root record parsed with exact cursor and individual read counts"
  let q := SpongefishCurrentModeQueries.coordinate after.pending 0
  if bounded : pathCost q ≤ 4096 then
    let raw := DuplexModeGame.constructionKey 4096 parameter q bounded
    let candidates := SpongefishCurrentRecordModeCapture.rawRecords record.shape parameter raw
    unless candidates.length ≤ 4 && candidates.any (fun r => openingBytes r = source) do
      throw (IO.userError "literal current raw coordinate lost the saved record")
    report "literal raw coordinate recovered the bounded saved-record candidates"
  else
    throw (IO.userError "current record exceeded the smoke query budget")
  let other := {record with root := fun i => if i.val = 0 then 1 else 0}
  unless (SpongefishRecordBindingParser.verify c cur other).isNone do
    throw (IO.userError "foreign raw root accepted")
  report "foreign raw root rejected"
  unless (SpongefishRecordBindingParser.verify c {cur with narg := source.take (source.length-1)} record).isNone do
    throw (IO.userError "truncated current record accepted")
  report "truncated record rejected"
  let bytes ← match DuplexRefinement.squeeze c after.state 37 with
    | .ok (_,bytes) => pure bytes
    | .error _ => throw (IO.userError "source squeeze failed")
  let projections := (List.range 2).map fun block =>
    DuplexFraming.withCoordinate c parameter
      (SpongefishCurrentModeQueries.coordinate after.pending block) fun out => Array.ofFn out
  for j in [:bytes.length] do
    let some digest := projections[j/32]? | throw (IO.userError "missing output block")
    let some expected := digest[j%32]? | throw (IO.userError "missing output byte")
    unless bytes[j]?.getD 0 = expected do
      throw (IO.userError s!"source output byte coordinate differs at {j}")
  IO.println s!"PASS current observed session derivation ({derived.view.observations.length} primitive calls), raw-root record ({after.bytesRead} bytes, {after.messagesRead} individual reads), foreign/truncated rejection, 37 projected output bytes"
  (← IO.getStdout).flush
