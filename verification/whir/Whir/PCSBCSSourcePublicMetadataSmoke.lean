import Whir.PCSBCSSourcePublicMetadata
import Whir.PCSBCSConstructionReplayTrace

namespace Whir.PCSBCSSourcePublicMetadataSmoke
open Whir Concrete Protocol FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open DuplexPublicSimulator RawOracleCoupling PublicCompressionProgram
open PCSBCSPublicCallerCompletion
open TypedOracleCompiler

local instance : CommRing E := FieldModel.instCommRingE
local instance : Zero E := ⟨E.zero⟩
local instance : One E := ⟨E.one⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

private def p : ParameterBounds.Profile := ⟨⟨0,by decide⟩,⟨0,by decide⟩⟩
private def layout : WHIRCallerClaims.CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩
private def digest (salt : Nat) : Digest32 := fun i =>
  ⟨(17*i.val+salt)%256,Nat.mod_lt _ (by decide)⟩
private def saved : AnchoredHeaderCodec.Record :=
  ⟨AnchoredSourceCaller.shape layout,digest 17,⟨digest 19,(fun _ => none),0,true,0,0⟩,
    E.ofK 3 :: List.replicate 14 0,E.ofK 23⟩
private def zeroToken : WHIRCallerShape.EventShape → WHIRCallerClaims.CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)
private def entryFor (record : AnchoredHeaderCodec.Record) : FramedHistory :=
  WHIRCallerClaims.tokenHistory (digest 11) (digest 13)
    (((WHIRCallerClaims.callerShape layout).drop (WHIRCallerClaims.rootScalarCount layout)).map
      zeroToken ++ (AnchoredHeaderCodec.openingScalars record).map WHIRCallerClaims.CallerToken.sent)

private def publicPath (cv : Digest32) (log : PublicLog) :
    List DuplexEncoding.Instruction → Option (PublicLog × Node)
  | [] => none
  | [(block,tweak)] => some (log,⟨cv,block,tweak,true⟩)
  | (block,tweak) :: next :: rest =>
    let node : Node := ⟨cv,block,tweak,true⟩
    let stored := Array.ofFn (blake2sOracle node)
    let answer : Digest32 := fun i => stored[i.val]'(by simp [stored])
    publicPath answer (DuplexPublicSimulator.observe log node answer) (next::rest)

private def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"public metadata completion: {label}")
  IO.println s!"public metadata completion PASS: {label}"

def smoke : IO Unit := do
  let originalEntry := entryFor saved
  let coordinate : Coordinate := ⟨originalEntry,.output 1⟩
  let iv := PCSBCSSourceCoordinateDecoder.seedIV
  let Q := pathCost coordinate
  let some (prefixLog,input) := publicPath iv [] (DuplexEncoding.plan coordinate)
    | throw (IO.userError "actual source path absent")
  let some metadata := PCSBCSSourcePublicMetadata.recover p Q originalEntry.frames.length prefixLog input
    | throw (IO.userError "actual primitive source metadata rejected")
  require "physical source inversion recovers every saved field, not a supplied header"
    (AnchoredHeaderCodec.openingScalars metadata.saved == AnchoredHeaderCodec.openingScalars saved)
  require "missing ancestral source record rejects metadata rather than fabricating a record"
    ((PCSBCSSourcePublicMetadata.recover p Q originalEntry.frames.length [] input).isNone)
  let outputs := WHIRCallerOutputs.callerOutputs originalEntry
  require "fixture has earlier caller outputs absent from the public source prefix"
    (outputs.any fun q => (PCSBCSPublicCallerAnswers.answer? prefixLog iv q).isNone)
  let completed := Sampling.execute blake2sOracle (callerCompletion iv prefixLog originalEntry)
  require "completion executes real compression plans for missing earlier outputs"
    (completed.2.length ≥ 2 && outputs.all fun q =>
      (PCSBCSPublicCallerAnswers.answer? completed.1 iv q).isSome)
  let duplicate := Sampling.execute blake2sOracle (callerCompletion iv completed.1 originalEntry)
  require "repeated earlier outputs are served from the recorded public cache"
    (duplicate.2.isEmpty)
  let some original := Sampling.eval blake2sOracle
      (PCSBCSSourcePublicMetadata.originalCompletion p layout iv originalEntry.frames.length
        metadata prefixLog (fun _ => digest 199))
    | throw (IO.userError "real completed original caller rejected")
  require "original reconstruction retains the public anchor and occupied lane geometry"
    (original.lanes == saved.shape.lanes && original.anchorPoint == saved.point.toArray &&
      original.anchorValue == saved.value)
  require "an incomplete getter cache rejects, even when an outside callback exists"
    ((PCSBCSSourcePublicMetadata.resolveOriginal p layout iv originalEntry.frames.length
      metadata prefixLog (fun _ => digest 199)).isNone)
  IO.println s!"public metadata completion: {outputs.length} earlier outputs, {completed.2.length} real draws"

end Whir.PCSBCSSourcePublicMetadataSmoke

def main : IO Unit := Whir.PCSBCSSourcePublicMetadataSmoke.smoke
