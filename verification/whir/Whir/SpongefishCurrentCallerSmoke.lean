import Whir.SpongefishCurrentSourceCallerOriginal
import Whir.SpongefishCurrentPhysicalModeCompiler

/-! Literal current-session caller reconstruction using real BLAKE2s replies.
The scalar payload and nonce are parser fixtures, not an accepted PCS opening
or a proof-of-work claim. The returned original is checked against the actual
received anchor and actual sampled caller point. -/
namespace Whir.SpongefishCurrentCallerSmoke
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames WHIRCallerClaims

local instance : Add E := ⟨E.add⟩
local instance : Mul E := ⟨E.mul⟩
local instance : Zero E := ⟨E.zero⟩
local instance : One E := ⟨E.one⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

def p : ParameterBounds.Profile := ⟨⟨0,by decide⟩,⟨0,by decide⟩⟩
def layout : CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩

private def report (label : String) : IO Unit := do
  IO.println s!"current caller: {label}"
  (← IO.getStdout).flush

private def proofBytes : List WHIRCallerShape.EventShape → List Byte
  | [] => []
  | .absorb n :: rest => List.replicate n 0 ++ proofBytes rest
  | .squeeze _ :: rest => proofBytes rest
  | .nonce _ :: rest => List.replicate 8 0 ++ proofBytes rest

private def allConstructed (observations : List Observation) : List Observation :=
  observations.filter fun o => match o.query with
    | .construction _ _ => true
    | .primitive _ _ => false

def smoke : IO Unit := do
  let C := DuplexModeGame.blake2sOracle
  let c := compressionOf C
  let parameter := DuplexCompression.parameterIV
  let tag : List Byte := [3,5]
  let instanceBytes : List Byte := [11,17]
  let shape := AnchoredSourceCaller.shape layout
  let preludeShape := SpongefishCurrentSourceCallerOriginal.preludeShape layout
  let payloadShape := SpongefishCurrentSourceCallerOriginal.payloadShape layout
  let some preludeCalls := SpongefishCurrentSourceCallerOriginal.shapeCalls preludeShape
    | throw (IO.userError "unsupported prelude fixture")
  let headBytes := SpongefishCurrentAnchorHeader.bytes shape zeroDigest ++ scalarBytes (E.ofK 9)
  let firstBytes := proofBytes preludeShape ++ headBytes ++ proofBytes payloadShape
  let some start := SpongefishCurrentObservedSessionEntry.actualSetup c parameter tag instanceBytes firstBytes []
    | throw (IO.userError "nonempty current session rejected")
  let .ok before := SpongefishCurrentPrimitiveEventCompiler.actualReplay c start preludeCalls
    | throw (IO.userError "actual prelude rejected")
  let some (_,record) := SpongefishCurrentCommitmentReceive.receive c before shape
    | throw (IO.userError "actual current header/anchor/value rejected")
  report "actual initialized prelude and raw-root anchor receive completed"
  let bindingBytes := (SpongefishRecordBindingParser.messages record).flatMap (fun message => message.bytes)
  let narg := firstBytes ++ bindingBytes
  let some callerCalls := SpongefishCurrentSourceCallerOriginal.calls layout record
    | throw (IO.userError "unsupported caller fixture")
  let source := runReal C parameter
    (SpongefishCurrentPhysicalModeCompiler.program parameter tag instanceBytes narg []
      (callerCalls ++ [.draw .fold]))
  let some (.ok captured) := source.view.result
    | throw (IO.userError "observed physical source caller rejected")
  report "observed physical compiler completed all caller and opening-record fields"
  let some (.ok beforeGamma) := SpongefishCurrentObservedSessionEntry.actualEntry c parameter tag
      instanceBytes narg [] callerCalls
    | throw (IO.userError "actual source caller rejected")
  unless captured.1.narg = [] && captured.1.bytesRead = narg.length &&
      beforeGamma.bytesRead = narg.length do
    throw (IO.userError "caller source transport differs")
  report "real initialized source consumed exact caller and binding bytes"
  let q := SpongefishCurrentModeQueries.coordinate beforeGamma.pending 0
  if work : pathCost q ≤ 1048576 then
    let raw := constructionKey 1048576 parameter q work
    let inputs := SpongefishCurrentSourceCallerOriginal.original p layout parameter raw
      instanceBytes source.view.observations
    let some input := inputs.find? (fun input => input.anchorPoint == record.point.toArray &&
        input.anchorValue == record.value)
      | throw (IO.userError "literal public source getter failed to reconstruct actual original")
    unless input.lanes = 16 && input.m = 1 && input.points.size = 0 &&
        input.prepared.familyWeights.size = 1 && input.prepared.familyTargets[0]!.size = 64 &&
        input.prepared.anchorTable.size = 32768 && input.prepared.anchorClaim.value = E.ofK 9 do
      throw (IO.userError "reconstructed original dimensions or literal values differ")
    if family : 0 < input.m then
      unless input.anchorPoint[0]! != (input.family ⟨0,family⟩).point[0]! do
        throw (IO.userError "actual independent caller point was not retained")
    else throw (IO.userError "literal caller family disappeared")
    report "public construction replies reconstructed actual anchor, caller point and original preparation"
    unless (SpongefishCurrentSourceCallerOriginal.original p layout parameter raw
        [99] source.view.observations).isEmpty do
      throw (IO.userError "foreign literal instance accepted")
    unless (SpongefishCurrentSourceCallerOriginal.original p layout parameter raw
        instanceBytes []).isEmpty do
      throw (IO.userError "missing public construction replies accepted")
    let constructed := allConstructed source.view.observations
    unless (SpongefishCurrentSourceCallerOriginal.original p layout parameter raw
        instanceBytes constructed).any (fun other => other.anchorPoint == input.anchorPoint &&
          other.anchorValue == input.anchorValue && other.m = input.m) do
      throw (IO.userError "ordinary primitive answers improperly substituted for construction replies")
    report "foreign instance and missing replies rejected; only literal construction observations used"
  else throw (IO.userError "fixture raw-key construction exceeded explicit cap")

end Whir.SpongefishCurrentCallerSmoke

def main : IO Unit := Whir.SpongefishCurrentCallerSmoke.smoke
