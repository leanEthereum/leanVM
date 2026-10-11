import Whir.PCSBCSMerkleRootCache
import Whir.PCSBCSMerkleFullSourceTransport

/-! Actual BLAKE2s records with occupied<leafWords, accepted full-wire opening,
local tampered-padding rejection, explicit unavailable status, immutable same
address, and identical-preimage interpretations at separate image shapes. -/
namespace Whir.MerkleQueryLogExtractionSmoke
open Concrete FiatShamirGame DuplexModeGame PublicMerkleLog MerkleTransport MerkleBinding
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PCSBCSMerkleLeafImages

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def smoke : IO Unit := do
  let left : List K := (List.range 9).map fun n => UInt64.ofNat (n+1)
  let right : List K := (List.range 9).map fun n => UInt64.ofNat (n+21)
  let fullLeft := leafImage 0 16 left
  let fullRight := leafImage 0 16 right
  let lb := ByteCodec.wordsBytes fullLeft
  let rb := ByteCodec.wordsBytes fullRight
  let ld := hashBlake2s lb
  let rd := hashBlake2s rb
  let pb := List.ofFn (ByteCodec.pairBytes (ld,rd))
  let root := hashBlake2s pb
  let honest := plan blake2sOracle lb ++ plan blake2sOracle rb ++ plan blake2sOracle pb
  let cells := sourceCells honest root 1 16 9
  let table := compactTable cells
  require ((imageTable cells).toList.map Array.toList == [fullLeft,fullRight])
    "full authenticated images lost their leading padding"
  require (table.toList.map Array.toList == [left,right]) "compact suffix rows differ"
  require (cells.toList.all (fun cell => cell.available && cell.paddingValid))
    "honest padded leaves did not carry both status bits"
  require ((root0Consumer 9 16 table)[0]!.toList == left.reverse ++ List.replicate 7 0)
    "separate first-fold occupied-lane reversal/padding differs"
  let fullProof : PrunedMerklePaths := ⟨[fullLeft,fullRight],[]⟩
  require ((PCSBCSMerkleFullSourceTransport.openSource hashBlake2s fullProof root
    2 [0,1] 16 9).isSome) "valid occupied<leafWords source opening was rejected"
  let badLeft := (1 : K) :: List.replicate 6 0 ++ left
  let badDigest := hashBlake2s (ByteCodec.wordsBytes badLeft)
  let badPair := List.ofFn (ByteCodec.pairBytes (badDigest,rd))
  let badRoot := hashBlake2s badPair
  let badProof : PrunedMerklePaths := ⟨[badLeft,fullRight],[]⟩
  require ((badProof.open hashBlake2s badRoot 2 [0,1] 16 16).isSome)
    "tampered-prefix test did not authenticate its own full bytes"
  require ((PCSBCSMerkleFullSourceTransport.openSource hashBlake2s badProof badRoot
    2 [0,1] 16 9).isNone) "nonzero authenticated padding was accepted by source gate"
  let badLog := plan blake2sOracle (ByteCodec.wordsBytes badLeft) ++
    plan blake2sOracle rb ++ plan blake2sOracle badPair
  let badCells := sourceCells badLog badRoot 1 16 9
  require ((compactTable badCells).toList.map Array.toList == [left,right])
    "invalid padding changed the literal suffix oracle"
  require (((badCells[0]?).map (fun cell => (cell.available,cell.paddingValid))) == some (true,false))
    "invalid padding was conflated with missing data or authenticated padding"
  let missing := plan blake2sOracle rb ++ plan blake2sOracle pb
  let mt := fromPublic missing root 1
  require (mt.get [false] == none && mt.get [true] == some fullRight)
    "missing full preimage was forged or available sibling was lost"
  let missingCells := sourceCells missing root 1 16 9
  require ((compactTable missingCells).toList.map Array.toList == [List.replicate 9 0,right])
    "explicit book default or compact table order differs"
  require (((missingCells[0]?).map (fun cell => (cell.available,cell.paddingValid))) == some (false,false))
    "unavailable zero default was authenticated"
  let registry := PCSBCSMerkleRootCache.register ∅ honest root ⟨1,16,9⟩
  let repeated := PCSBCSMerkleRootCache.register registry missing root ⟨1,16,9⟩
  let physicalKey := PCSBCSMerkleRootCache.cacheKey root ⟨1,16,9⟩
  require ((repeated[physicalKey]?).map (fun frozen => frozen.raw.toList.map Array.toList) ==
    some [left,right]) "same-shape first registration was recomputed or replaced"
  require ((repeated[physicalKey]?).map (fun frozen => frozen.queryPrefix.length) ==
    some honest.length) "same-shape announcement prefix changed"
  let some pairWords := decodeWords pb | throw (IO.userError "pair did not decode as eight words")
  require (pairWords.length == 8 && ByteCodec.wordsBytes pairWords == pb)
    "identical-preimage reinterpretation changed the bytes"
  let alternate := PCSBCSMerkleRootCache.register repeated honest root ⟨0,8,8⟩
  let alternateKey := PCSBCSMerkleRootCache.cacheKey root ⟨0,8,8⟩
  require ((alternate[alternateKey]?).map (fun frozen => frozen.raw.toList.map Array.toList) ==
    some [pairWords]) "same CV at another image shape reused the old table"
  let alternateProof : PrunedMerklePaths := ⟨[pairWords],[]⟩
  require ((PCSBCSMerkleFullSourceTransport.openSource hashBlake2s alternateProof root
    1 [0] 8 8).isSome) "identical-preimage alternate shape was not actually admitted"
  let narrow := PCSBCSMerkleRootCache.register alternate honest root ⟨1,16,8⟩
  let narrowKey := PCSBCSMerkleRootCache.cacheKey root ⟨1,16,8⟩
  require ((narrow[narrowKey]?).map (fun frozen => frozen.raw.toList.map Array.toList) ==
    some [left.drop 1,right.drop 1]) "another occupied width lost the literal suffix"
  let wider := PCSBCSMerkleRootCache.register narrow honest root ⟨1,32,9⟩
  let widerKey := PCSBCSMerkleRootCache.cacheKey root ⟨1,32,9⟩
  require ((wider[widerKey]?).map (fun frozen => frozen.raw.toList.map Array.toList) ==
    some [List.replicate 9 0,List.replicate 9 0]) "image width was omitted from the address"
  require ((wider[widerKey]?).map (fun frozen => frozen.cells.toList.all (fun c => !c.available)) ==
    some true) "wrong-width defaults were marked available"
  require (wider.size == 4) "five announcements of one CV did not create four addressed entries"
  require ((wider[physicalKey]?).map (fun frozen => frozen.raw.toList.map Array.toList) ==
    some [left,right]) "another image shape replaced the original table"
  let tampered : PublicLog := honest.map fun e =>
    if e.1 = node DuplexCompression.parameterIV 0 pb true then (e.1,ld) else e
  require ((fromPublic tampered root 1).get [false] == none) "tampered root answer was accepted"
  require (decodeWords [0] == none && parsePair [0] == none) "malformed bytes were accepted"
  let collisionRecords : MerkleTransport.Commitments.Records := [(lb,ld),(rb,ld)]
  let indexed := build collisionRecords
  require (indexed[key ld]? == some lb) "first collision registration was not retained"
  require ((register indexed rb ld)[key ld]? == some lb) "collision registration was overwritten"
  require ((extract canonicalCodec indexed 0 ld).get [] == some fullLeft) "collision case was not deterministic"
  IO.println "Merkle query-log extraction smoke PASS (padded-source/opening/padding-rejection/absence/collision/lane-order/image-address)"

end Whir.MerkleQueryLogExtractionSmoke

def main : IO Unit := Whir.MerkleQueryLogExtractionSmoke.smoke
