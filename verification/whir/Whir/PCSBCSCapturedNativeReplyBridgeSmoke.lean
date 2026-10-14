import Whir.PCSBCSCapturedNativeReplyBridge

/-! Real BLAKE2s full padded source opening, native codec projection and exact
chronological captured inverse. These finite executions exercise the native
formal-model transport path, not a universal Rust/Aeneas refinement. -/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedNativeReplyBridgeSmoke
open Concrete Protocol CausalGame CausalProbability WHIRHistory FiatShamirGame
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open PCSBCSSourceFrozenAccessor PCSBCSCapturedNativeReplyBridge
open MerkleTransport PublicMerkleLog DuplexModeGame
open AnchoredHeaderCodec

private def toy : Config := ⟨3,#[1,1],#[1,1],#[3,3],#[0,0]⟩
private def digest (n : Nat) : Digest32 := fun i => ⟨(n / 256^i.val)%256,Nat.mod_lt _ (by decide)⟩
private def recordedTree (extension : Bool) (missing : Option Nat) :
    Nat → Nat → Digest32 × DuplexPublicSimulator.PublicLog
  | 0,start =>
    let words : List K := if extension then [UInt64.ofNat (100+start),200,300,400,500,600]
      else [0,UInt64.ofNat (10+start)]
    let bytes := ByteCodec.wordsBytes words
    (hashBlake2s bytes,if missing == some start then [] else plan blake2sOracle bytes)
  | height+1,start =>
    let l := recordedTree extension missing height start
    let r := recordedTree extension missing height (start+2^height)
    let bytes := List.ofFn (ByteCodec.pairBytes (l.1,r.1))
    (hashBlake2s bytes,l.2 ++ r.2 ++ plan blake2sOracle bytes)

private def firstTree := recordedTree false none 3 0
private def nextTree := recordedTree true none 2 0
private def saved : Record :=
  ⟨⟨3,1,1,1⟩,firstTree.1,⟨digest 0,fun _ => none,0,true,0,0⟩,[0,0,0],0⟩
private def firstRef : Reference := ⟨saved.root,initialShape saved.shape⟩
private def nextRef : Reference := ⟨nextTree.1,phaseShape toy 1⟩
private def rootFrozen : Frozen := freeze firstTree.2 firstRef.root firstRef.shape
private def nextFrozen : Frozen := freeze nextTree.2 nextRef.root nextRef.shape
private def registry : Captures := fun ref =>
  if ref = firstRef then some rootFrozen else if ref = nextRef then some nextFrozen else none
private def query : Coordinate toy := .query ⟨0,by decide⟩
private def boundary : Coordinate toy := .fold ⟨0,by decide⟩ ⟨0,by decide⟩
private def current : Coordinate toy := .query ⟨1,by decide⟩
private def tape : Tape toy :=
  (coordinates toy).symm fun q => match q with
  | .query _ => (fun _ => (⟨219,20,21⟩ : E),0)
  | _ => 0
private def past : WHIRFiatShamir.Prefix current := WHIRFiatShamir.Prefix.ofTape current tape
private def fields (q : Coordinate toy) : List E :=
  match q with
  | .fold i j => [0,0] ++ if j.val+1 = toy.folds[i.val]! then
      if i.val+1 < toy.folds.size then rootScalars nextRef.root
      else List.replicate (2^remaining toy i.val) 0
    else []
  | .ood _ _ => [0,0,0]
  | _ => [0,0]
private def messages : List Pending :=
  ((List.range (position current+1)).map fun n =>
    (⟨if n = 0 then [] else fields (((schedule toy)[n-1]?).getD .initial),
      match ((schedule toy)[n]?).getD .initial with
      | .query _ => some (0,0)
      | _ => none⟩ : Pending)).reverse

private def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"native reply bridge: {label}")
  IO.println s!"native reply bridge PASS: {label}"

private def queryProof : PrunedMerklePaths :=
  ⟨[[0,13],[0,17]],[(recordedTree false none 0 2).1,(recordedTree false none 0 6).1,
    (recordedTree false none 1 0).1,(recordedTree false none 1 4).1]⟩

private def extensionProof : PrunedMerklePaths :=
  ⟨[[101,200,300,400,500,600],[102,200,300,400,500,600]],
    [(recordedTree true none 0 0).1,(recordedTree true none 0 3).1]⟩

private def openingRows (phase leafWords occupied : Nat) (paths : List RawPath) : Option Oracle :=
  (paths.mapM (fun path => rowCodec phase (path.leafData.drop (leafWords-occupied)).toArray)).map List.toArray

private def paddedTree (bad : Nat) : Nat → Nat → Digest32 × DuplexPublicSimulator.PublicLog
  | 0,start =>
    let words : List K := [if start = bad then 9 else 0,UInt64.ofNat (10+start)]
    let bytes := ByteCodec.wordsBytes words
    (hashBlake2s bytes,plan blake2sOracle bytes)
  | h+1,start =>
    let l := paddedTree bad h start
    let r := paddedTree bad h (start+2^h)
    let bytes := List.ofFn (ByteCodec.pairBytes (l.1,r.1))
    (hashBlake2s bytes,l.2 ++ r.2 ++ plan blake2sOracle bytes)

private def requireQuery (saved' : AnchoredHeaderCodec.Record) (registry' : Captures)
    (native : Oracle) : IO Unit := do
  match inverseAt current saved' registry' messages past (position query) with
  | none => throw (IO.userError "native chronological query inverse rejected")
  | some inverted => match inverted.reply with
    | .query rows m =>
      require "accepted native query equals captured inverse including duplicates and nonce"
        (rows == native && m.u0 == 0 && m.u2 == 0 &&
          inverted.nonce == (messages.reverse[position query+1]?).bind Pending.nonce)
    | _ => throw (IO.userError "native chronological query inverse wrong tag")

def smoke : IO Unit := do
  let qs := [3,7,3]
  let opened ← match PCSBCSMerkleFullSourceTransport.openSource hashBlake2s queryProof
      firstRef.root 8 qs 2 1 with
    | some paths => pure paths
    | none => throw (IO.userError "actual padded base source opening rejected")
  let native ← match openingRows 0 2 1 opened with
    | some rows => pure rows
    | none => throw (IO.userError "actual accepted base suffix codec rejected")
  require "full padded opening preserves derived repeated order"
    (opened.map RawPath.leafIndex == qs && native == #[#[E.ofK 13],#[E.ofK 17],#[E.ofK 13]])
  requireQuery saved registry native
  require "wrong root rejects actual BLAKE2s opening"
    (PCSBCSMerkleFullSourceTransport.openSource hashBlake2s queryProof (digest 99) 8 qs 2 1).isNone
  require "missing source proof row rejects rather than zero authenticating"
    (PCSBCSMerkleFullSourceTransport.openSource hashBlake2s
      ⟨[[0,13]],queryProof.siblingHashes⟩ firstRef.root 8 qs 2 1).isNone
  require "missing first capture rejects chronological inverse"
    (inverseAt current saved (fun _ => none) messages past (position query)).isNone
  let incomplete := recordedTree false (some 3) 3 0
  let ghost := freeze incomplete.2 firstRef.root firstRef.shape
  let ghostAccess ← match build current saved
      (fun ref => if ref = firstRef then some ghost else registry ref) messages past query ⟨[0,0],none⟩ with
    | some a => pure a
    | none => throw (IO.userError "ghost source storage selection rejected")
  require "unavailable repeated ghost cells cannot match accepted native rows or authenticate"
    (ghostAccess.rows != native && ghostAccess.selectedStatus[0]! == ⟨false,false⟩ &&
      ghostAccess.selectedStatus[2]! == ⟨false,false⟩)
  let bad := paddedTree 3 3 0
  let badSaved := {saved with root := bad.1}
  let badRef : Reference := ⟨bad.1,firstRef.shape⟩
  let badFrozen := freeze bad.2 bad.1 badRef.shape
  let badProof : PrunedMerklePaths := ⟨[[9,13],[0,17]],queryProof.siblingHashes⟩
  require "real nonzero padding hashes to its own root but source opening rejects"
    ((badProof.open hashBlake2s bad.1 8 qs 2 2).isSome &&
      (PCSBCSMerkleFullSourceTransport.openSource hashBlake2s badProof bad.1 8 qs 2 1).isNone)
  require "available bad padding rejects actual captured chronological inverse"
    (inverseAt current badSaved (fun ref => if ref = badRef then some badFrozen else registry ref)
      messages past (position query)).isNone
  let tail : Coordinate toy := .tail ⟨0,by decide⟩
  let tailPast := WHIRFiatShamir.Prefix.ofTape tail tape
  let tailMessages := (⟨[0,0],none⟩ : Pending) :: messages
  let extensionOpened ← match PCSBCSMerkleFullSourceTransport.openSource hashBlake2s
      extensionProof nextRef.root 4 [1,2,1] 6 6 with
    | some paths => pure paths
    | none => throw (IO.userError "actual extension source opening rejected")
  let extensionNative ← match openingRows 1 6 6 extensionOpened with
    | some rows => pure rows
    | none => throw (IO.userError "actual extension native codec rejected")
  match inverseAt tail saved registry tailMessages tailPast (position current) with
  | some inverted => match inverted.reply with
    | .query rows _ =>
      require "extension accepted reply transports exact consecutive triples and duplicates"
        (rows == extensionNative && rows.size == 3 && rows[0]! == rows[2]!)
    | _ => throw (IO.userError "extension query tag mismatch")
  | none => throw (IO.userError "extension captured query inverse rejected")
  let fullNext : PrunedMerklePaths := ⟨(List.range 4).map (fun n =>
    [UInt64.ofNat (100+n),200,300,400,500,600]),[]⟩
  let fullOpened ← match PCSBCSMerkleFullSourceTransport.openSource hashBlake2s fullNext
      nextRef.root 4 [0,1,2,3] 6 6 with
    | some paths => pure paths
    | none => throw (IO.userError "full next source table opening rejected")
  let fullNative ← match openingRows 1 6 6 fullOpened with
    | some rows => pure rows
    | none => throw (IO.userError "full next source table codec rejected")
  match inverseAt current saved registry messages past (position boundary) with
  | some inverted => match inverted.reply with
    | .fold _ (some next) residual =>
      require "nonterminal fold transports full next table rather than query subset"
        (next == fullNative && next.size == 4 && residual.isEmpty && nextFrozen.cells.all (·.available))
    | _ => throw (IO.userError "nonterminal fold tag mismatch")
  | none => throw (IO.userError "nonterminal captured inverse rejected")
  require "missing next capture rejects nonterminal fold"
    (inverseAt current saved (fun ref => if ref = firstRef then some rootFrozen else none)
      messages past (position boundary)).isNone
  require "wrong/missing full next opening rejects"
    ((PCSBCSMerkleFullSourceTransport.openSource hashBlake2s fullNext (digest 88) 4 [0,1,2,3] 6 6).isNone &&
      (PCSBCSMerkleFullSourceTransport.openSource hashBlake2s ⟨fullNext.leafData.drop 1,[]⟩
        nextRef.root 4 [0,1,2,3] 6 6).isNone)
  require "malformed extension suffix does not drop limbs" (rowCodec 1 #[1,2]).isNone

end Whir.PCSBCSCapturedNativeReplyBridgeSmoke

def main : IO Unit := Whir.PCSBCSCapturedNativeReplyBridgeSmoke.smoke
