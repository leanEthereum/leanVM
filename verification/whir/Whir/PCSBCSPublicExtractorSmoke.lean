-- This compiled regression exercises the public extractor and real BLAKE2s.
-- It does not assert accepted Rust-verifier execution or universal compiler refinement.
import Whir.PCSBCSPublicExtractor
import Whir.PublicMerkleProgram
import Whir.AnchoredSourceFreshCaller
open Whir Concrete Protocol FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicMerkleLog AnchoredHeaderCodec WHIRCallerRegistry WHIRCallerShape WHIRCallerClaims
set_option autoImplicit false
private def p : ParameterBounds.Profile := (⟨0,by decide⟩,⟨0,by decide⟩)
private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val)%256,Nat.mod_lt _ (by decide)⟩
private def layout : WHIRCallerClaims.CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩
private def zeroToken : WHIRCallerShape.EventShape → CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)
private def require (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
  IO.println s!"public extractor: {label}"
  (← IO.getStdout).flush
private def observation (q : Coordinate) : Option Observation :=
  if valid : DuplexEncoding.Admissible q then
    withCoordinate (compressionOf blake2sOracle) PCSBCSSourceCoordinateDecoder.seedIV q
      fun answer => some ⟨.construction q valid,answer⟩
  else none

def main : IO Unit := do
  IO.println "public extractor: entering main"
  (← IO.getStdout).flush
  let smallDomain := ConcreteRowExtraction.domain 2 (by decide)
  let mixed : Vector E smallDomain.n := Vector.ofFn fun i => smallDomain.val[i.val]!
  let linear := ConcreteRowExtraction.countedExtractRow 1 1 (by decide) mixed
  require (linear.1 == some #[0,1]) "mixed zero/nonzero row recovered the linear base word"
  let config := ParameterBounds.config p
  let shape := AnchoredSourceCaller.shape layout
  let fullWords := List.replicate (2^shape.logBatch) (0 : K)
  let leafBytes := ByteCodec.wordsBytes fullWords
  let mut records := plan blake2sOracle leafBytes
  let some (_,root) := records.getLast? | throw (IO.userError "empty leaf primitive plan")
  let mut current := root
  IO.println "public extractor: leaf primitive plan materialized"
  (← IO.getStdout).flush
  for _ in [: (PCSBCSSourceRootReferences.initialShape shape).height] do
    let bytes := List.ofFn (ByteCodec.pairBytes (current,current))
    let nodes := plan blake2sOracle bytes
    let some (_,root) := nodes.getLast? | throw (IO.userError "empty node primitive plan")
    current := root
    records := nodes ++ records
  IO.println "public extractor: physical Merkle image materialized"
  (← IO.getStdout).flush
  let saved : Record := ⟨shape,current,⟨digest 41,fun _=>none,0,true,0,0⟩,
    List.replicate config.logN 0,0⟩
  require (decide saved.Valid) "supported immutable shape"
  let payload := ((WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout)).map zeroToken
  let entry := tokenHistory (digest 11) (digest 13)
    (payload ++ (openingScalars saved).map CallerToken.sent)
  let opening := WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth config)
    entry [WHIRHistoryKey.initialPending] 1
  let fake := {opening with terminal := .output 100}
  let ordinary := records.reverse.map fun (n,d) =>
    (⟨.primitive .verification n,d⟩ : Observation)
  let caller := (WHIRCallerOutputs.callerOutputs entry).filterMap observation
  let some openingObservation := observation opening | throw (IO.userError "invalid opening coordinate")
  let some fakeObservation := observation fake | throw (IO.userError "invalid fake coordinate")
  let view : View Unit := {observations := ordinary ++ caller ++ [fakeObservation,openingObservation],result := ()}
  IO.println "public extractor: caller observations materialized"
  (← IO.getStdout).flush
  let B := 4096
  let ref : PCSBCSSourceRootReferences.Reference :=
    ⟨saved.root,PCSBCSSourceRootReferences.initialShape saved.shape⟩
  let some original := PCSBCSNativePublicCapture.publicOriginal p layout saved entry view
    | throw (IO.userError "public original did not parse")
  require (original.lanes == 16 && original.m == 1 && original.points.isEmpty) "literal original statement recovered"
  let rawFake : PublicCompressionCouplingMixed.Key B ←
    if bound : pathCost fake ≤ B then
      pure (.inr (constructionKey B PCSBCSSourceCoordinateDecoder.seedIV fake bound))
    else throw (IO.userError "source path exceeds the smoke budget")
  require ((PCSBCSPublicExtractor.rawReferences p B PCSBCSSourceCoordinateDecoder.seedIV
    entry.frames.length rawFake).isEmpty) "out-of-packet block cannot trigger first-root capture"
  let some captured := PCSBCSPublicExtractor.capturedPrefix p B PCSBCSSourceCoordinateDecoder.seedIV
    entry.frames.length ref view | throw (IO.userError "initial root not captured")
  require (captured.any (fun event => decide (event.1 = rawFake))) "genuine first mention follows fake prequery"
  let raw := PCSBCSPublicExtractor.root p B PCSBCSSourceCoordinateDecoder.seedIV
    entry.frames.length ref view
  require (raw.size == 2^ref.shape.height && raw.all (fun row=>row == Array.replicate shape.lanes 0))
    "full zero-prefix leaves decoded before compacting"
  IO.println "public extractor: starting production-profile Gao/original decoder"
  (← IO.getStdout).flush
  let result := PCSBCSPublicExtractor.extract p B PCSBCSSourceCoordinateDecoder.seedIV
    entry.frames.length layout saved entry ref view
  let some output := result | throw (IO.userError "supported zero word not extracted")
  require ((Array.ofFn output.2).all (fun word=>word == 0)) "production-profile word extracted from public view"
  let changedFamily := fun i => {original.family i with slices := fun _ => 1}
  require ((PCSRoundByRoundKnowledge.extract p original.lanes changedFamily original.points
    original.anchorPoint original.anchorValue raw).isNone)
    "false original family rejected without batching coins"
  IO.println "public extractor runtime PASS (actual BLAKE2s, fixed raw-key packet range, live caller observation decoding, production profile, compact occupied suffix, full word and false original)"
  (← IO.getStdout).flush
