import Whir.PCSBCSPublicLogExtractor

/-! Actual BLAKE2s source-key recovery and first-image capture. The incomplete
prefix is a local missing-record fixture, not an ideal-oracle probability test. -/
namespace Whir.PCSBCSPublicLogExtractorSmoke
open Whir Concrete Protocol FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicMerkleLog AnchoredHeaderCodec

private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val)%256,Nat.mod_lt _ (by decide)⟩

private def publicPath (cv : Digest32) (log : PublicLog) :
    List DuplexEncoding.Instruction → Option (PublicLog × Node)
  | [] => none
  | [(block,tweak)] => some (log,⟨cv,block,tweak,true⟩)
  | (block,tweak)::next::rest =>
    let input : Node := ⟨cv,block,tweak,true⟩
    let stored := Array.ofFn (blake2sOracle input)
    let answer : Digest32 := fun i => stored[i.val]'(by simp [stored])
    publicPath answer (Whir.DuplexPublicSimulator.observe log input answer) (next::rest)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def p : ParameterBounds.Profile := (⟨0,by decide⟩,⟨0,by decide⟩)
def smoke : IO Unit := do
  let words : List (List K) := [[0,3],[0,5],[0,7],[0,11]]
  let bytes := words.map ByteCodec.wordsBytes
  let leaves := bytes.map hashBlake2s
  let leftBytes := List.ofFn (ByteCodec.pairBytes (leaves[0]!,leaves[1]!))
  let rightBytes := List.ofFn (ByteCodec.pairBytes (leaves[2]!,leaves[3]!))
  let rootBytes := List.ofFn (ByteCodec.pairBytes (hashBlake2s leftBytes,hashBlake2s rightBytes))
  let root := hashBlake2s rootBytes
  let leafLogs := bytes.map (plan blake2sOracle)
  let incomplete := (leafLogs.drop 1).flatten ++ plan blake2sOracle leftBytes ++
    plan blake2sOracle rightBytes ++ plan blake2sOracle rootBytes
  let shape : Shape := ⟨2,1,1,1⟩
  let domain := digest 7
  let statement := digest 9
  let iv := PCSBCSSourceCoordinateDecoder.seedIV
  let history : FramedHistory := ⟨domain,statement,
    [.absorb 0 (WHIRHistory.scalarBytes (headerScalars shape root))]⟩
  let key : FiatShamirGame.Coordinate := ⟨history,.output 0⟩
  let some (queryPrefix,input) := publicPath iv incomplete (DuplexEncoding.plan key)
    | throw (IO.userError "empty anchored public source path")
  let target : Record := ⟨shape,root,⟨digest 41,fun _ => none,0,true,0,0⟩,[0,0],0⟩
  require (decide target.Valid) "invalid local immutable target"
  let registry :=
    (⟨iv,domain,fun s => if s = statement then some shape else none⟩ : AnchoredHeaderRoots.Public)
  let refs := PCSBCSSourcePrimitiveRootBudget.references p 64 0 registry queryPrefix input
  let childKey := {key with terminal := .output 1}
  let some (childPrefix,childInput) := publicPath iv incomplete (DuplexEncoding.plan childKey)
    | throw (IO.userError "empty child-block source path")
  let childLog := Whir.DuplexPublicSimulator.observe childPrefix childInput (blake2sOracle childInput)
  require ((PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry target childLog) == some childPrefix)
    "later point block did not capture the root before its own first disclosure"
  require (refs.length == 1 && refs.all (fun r => decide
    (r = ⟨root,PCSBCSSourceRootReferences.initialShape shape⟩)))
    "actual commitment key did not select its complete-image address"
  let received := Whir.DuplexPublicSimulator.observe queryPrefix input (blake2sOracle input)
  let some captured := PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry target received | throw (IO.userError "public anchor root was not captured")
  require (decide (captured = queryPrefix)) "capture included its challenge answer"
  let first := Whir.PCSBCSMerkleRootCache.freeze captured root (PCSBCSSourceRootReferences.initialShape shape)
  require (((first.cells[0]?).map (fun cell => cell.available)) == some false &&
    ((first.cells[1]?).map (fun cell => cell.available)) == some true)
    "missing prefix image was authenticated or an available sibling was lost"
  let later := plan blake2sOracle bytes[0]! ++ received
  let changed := Whir.DuplexPublicSimulator.observe queryPrefix input (digest 123)
  require ((PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry target later) == some captured)
    "later image queries replaced the first captured prefix"
  require ((PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry target changed) == some captured)
    "current whole answer changed the captured metadata"
  let some stable := PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry target later | throw (IO.userError "later log lost an existing capture")
  require (((((Whir.PCSBCSMerkleRootCache.freeze stable root (PCSBCSSourceRootReferences.initialShape shape)).cells[0]?).map
    (fun cell => cell.available))) == some false)
    "future leaf preimage entered the straight-line extraction table"
  let foreign := { target with root := digest 42 }
  require ((PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry foreign received).isNone) "unmentioned target root was invented"
  let config := ParameterBounds.config p
  let decodedShape : Shape := ⟨config.logN,config.folds[0]!,config.rates[0]!,1⟩
  let decodedTarget : Record :=
    ⟨decodedShape,root,⟨digest 41,fun _ => none,0,true,0,0⟩,
      List.replicate config.logN 0,0⟩
  require (decide decodedTarget.Valid) "invalid supported opening fixture"
  let decodedEntry := WHIRHistory.encodeHistory
    ⟨domain,statement,[.absorb 0 (openingScalars decodedTarget)]⟩
  let openingKey := WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth config)
    decodedEntry [WHIRHistoryKey.initialPending] 0
  let some (openingPrefix,openingInput) := publicPath iv incomplete (DuplexEncoding.plan openingKey)
    | throw (IO.userError "empty literal saved-opening path")
  let openingRefs := PCSBCSSourcePrimitiveRootBudget.references p 64 decodedEntry.frames.length
    registry openingPrefix openingInput
  require (openingRefs.length == 1 && openingRefs.all (fun r => decide
    (r = ⟨root,PCSBCSSourceRootReferences.initialShape decodedShape⟩)))
    "literal saved opening failed conservative role recovery"
  let openingLog := Whir.DuplexPublicSimulator.observe openingPrefix openingInput
    (blake2sOracle openingInput)
  require ((PCSBCSPublicLogExtractor.selectPrefix p 64 decodedEntry.frames.length registry
    decodedTarget openingLog) == some openingPrefix) "decoded saved opening not captured before reply"
  require ((PCSBCSPublicLogExtractor.selectPrefix p 64 decodedEntry.frames.length registry
    target openingLog).isNone) "equal roots at different shapes shared a cache address"
  IO.println "public-log extractor smoke PASS (real BLAKE2s, anchored address, before-answer capture, unavailable status, future/current independence)"

end Whir.PCSBCSPublicLogExtractorSmoke

def main : IO Unit := Whir.PCSBCSPublicLogExtractorSmoke.smoke
