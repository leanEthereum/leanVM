import Whir.PCSBCSSourceFrozenAccessor

/-! Toy geometry, actual BLAKE2s primitive records, frozen reconstruction,
source codecs/deriveQueries and checked reply inverse. Tampered copies exercise
local rejection/status handling, not a mocked security experiment. This is not
an accepted-path authenticity theorem or Fiat-Shamir endpoint. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceFrozenAccessorSmoke
open Concrete Protocol CausalGame CausalProbability WHIRHistory FiatShamirGame
open AnchoredHeaderCodec PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open PCSBCSSourceRootReferences PCSBCSSourceFrozenAccessor
open DuplexModeGame PublicMerkleLog

def toy : Config := ⟨3,#[1,1],#[1,1],#[3,3],#[0,0]⟩
def digest (n : Nat) : Digest32 := fun i => ⟨(n / 256^i.val)%256,Nat.mod_lt _ (by decide)⟩
def recordedTree (extension : Bool) (missing : Option Nat) :
    Nat → Nat → Digest32 × DuplexPublicSimulator.PublicLog
  | 0, start =>
    let words : List K := if extension then
      [UInt64.ofNat (100+start),200,300,400,500,600]
      else [0,UInt64.ofNat (10+start)]
    let bytes := ByteCodec.wordsBytes words
    (hashBlake2s bytes,if missing == some start then [] else plan blake2sOracle bytes)
  | height+1, start =>
    let left := recordedTree extension missing height start
    let right := recordedTree extension missing height (start+2^height)
    let bytes := List.ofFn (ByteCodec.pairBytes (left.1,right.1))
    (hashBlake2s bytes,left.2 ++ right.2 ++ plan blake2sOracle bytes)

def firstTree := recordedTree false none 3 0
def nextTree := recordedTree true none 2 0
def saved : Record :=
  ⟨⟨3,1,1,1⟩,firstTree.1,⟨digest 0,fun _ => none,0,true,0,0⟩,[0,0,0],0⟩
def firstRef : Reference := ⟨saved.root,initialShape saved.shape⟩
def nextRef : Reference := ⟨nextTree.1,phaseShape toy 1⟩
def rootFrozen : Frozen := freeze firstTree.2 firstRef.root firstRef.shape
def nextFrozen : Frozen := freeze nextTree.2 nextRef.root nextRef.shape
def initialCells : Array ImageCell := rootFrozen.cells
def registry : Captures := fun ref =>
  if ref = firstRef then some rootFrozen else if ref = nextRef then some nextFrozen else none

def query : Coordinate toy := .query ⟨0,by decide⟩
def boundary : Coordinate toy := .fold ⟨0,by decide⟩ ⟨0,by decide⟩
def current : Coordinate toy := .query ⟨1,by decide⟩
def tape : Tape toy :=
  (coordinates toy).symm fun q => match q with
  | .query _ => (fun _ => (⟨219,20,21⟩ : E),0)
  | _ => 0
def past : WHIRFiatShamir.Prefix current := WHIRFiatShamir.Prefix.ofTape current tape

def fields (q : Coordinate toy) : List E :=
  match q with
  | .fold i j => [0,0] ++ if j.val+1 = toy.folds[i.val]! then
      if i.val+1 < toy.folds.size then rootScalars nextRef.root
      else List.replicate (2^remaining toy i.val) 0
    else []
  | .ood _ _ => [0,0,0]
  | _ => [0,0]
def messages : List Pending :=
  ((List.range (position current+1)).map fun n =>
    (⟨if n = 0 then [] else fields (((schedule toy)[n-1]?).getD .initial),
      match ((schedule toy)[n]?).getD .initial with
      | .query _ => some (0,0)
      | _ => none⟩ : Pending)).reverse

def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"frozen accessor: {label}")
  IO.println s!"frozen accessor PASS: {label}"

def smoke : IO Unit := do
  check "immutable saved record and admitted source Pending prefix"
    (decide saved.Valid && scheduledAdmissible toy messages)
  check "query derivation reads all three E limbs, not only the base limb"
    (deriveQueries 64 3 #[⟨3,7,11⟩] == some #[3,2^63+7,11])
  let a ← match build current saved registry messages past query ⟨[0,0],none⟩ with
    | none => throw (IO.userError "query construction rejected")
    | some a => pure a
  IO.println s!"derived query order {a.queries.toList}"
  check "derived repeated order [3,7,3], not full oracle and not current Raw"
    (a.queries == #[3,7,3] && a.rows == #[#[E.ofK 13],#[E.ofK 17],#[E.ofK 13]])
  check "padded initial images retain compact live suffix only"
    (a.rows.all (fun row => row.size == 1) && a.selectedStatus.all
      (fun s => s.available && s.paddingValid))
  match inverseAt current saved registry messages past (position query) with
  | some r => match r.reply with
    | .query rows _ => check "source reply inverse integrates compact query rows" (rows == a.rows)
    | _ => throw (IO.userError "query inverse tag")
  | none => throw (IO.userError "query source inverse rejected")
  let folded ← match inverseAt current saved registry messages past (position boundary) with
    | some r => pure r
    | none => throw (IO.userError "fold source inverse rejected")
  match folded.reply with
  | .fold _ (some next) residual =>
    check "announced next CV uses full next-phase E extension oracle"
      (next.size == 4 && next[0]! == #[⟨100,200,300⟩,⟨400,500,600⟩] && residual.isEmpty)
  | _ => throw (IO.userError "fold inverse normalization")
  let tail : Coordinate toy := .tail ⟨0,by decide⟩
  let laterPast := WHIRFiatShamir.Prefix.ofTape tail tape
  let laterMessages := (⟨[0,0],none⟩ : Pending) :: messages
  let extension ← match build tail saved registry laterMessages laterPast current ⟨[0,0],none⟩ with
    | some a => pure a
    | none => throw (IO.userError "later-phase query construction rejected")
  check "later-phase compact query rows decode consecutive E triples with repeated order"
    (extension.queries == #[1,2,1] && extension.rows ==
      #[#[⟨101,200,300⟩,⟨400,500,600⟩],#[⟨102,200,300⟩,⟨400,500,600⟩],
        #[⟨101,200,300⟩,⟨400,500,600⟩]])
  let missingNextTree := recordedTree true (some 0) 2 0
  let unavailableNext := freeze missingNextTree.2 nextRef.root nextRef.shape
  let ghostNext ← match build current saved
      (fun ref => if ref = nextRef then some unavailableNext else registry ref)
      messages past boundary ⟨fields boundary,none⟩ with
    | some a => pure a
    | none => throw (IO.userError "unavailable full next oracle rejected")
  check "full next oracle retains unavailable zero cells and explicit status"
    (ghostNext.next[0]! == #[0,0] && ghostNext.nextStatus[0]! == ⟨false,false⟩)
  check "missing initial capture rejects"
    (build current saved (fun _ => none) messages past query ⟨[0,0],none⟩).isNone
  check "missing announced next capture rejects"
    (inverseAt current saved (fun ref => if ref = firstRef then some rootFrozen else none)
      messages past (position boundary)).isNone
  check "current and future query index rejects"
    ((inverseAt current saved registry messages past (position current)).isNone &&
      (inverseAt current saved registry messages past 100).isNone)
  let badCell := leafCell 2 1 [1,13]
  let badCells := initialCells.set! 3 badCell
  let badRoot : Frozen := ⟨firstRef.shape,[],badCells,compactTable badCells⟩
  check "selected invalid padding rejects instead of authenticated zero"
    (build current saved (fun ref => if ref = firstRef then some badRoot else registry ref)
      messages past query ⟨[0,0],none⟩).isNone
  let unqueriedCells := initialCells.set! 0 (leafCell 2 1 [1,10])
  let unqueriedBad : Frozen := ⟨firstRef.shape,[],unqueriedCells,compactTable unqueriedCells⟩
  check "unqueried bad padding does not globally reject a ghost root"
    (build current saved (fun ref => if ref = firstRef then some unqueriedBad else registry ref)
      messages past query ⟨[0,0],none⟩).isSome
  let missingFirstTree := recordedTree false (some 3) 3 0
  let partialRoot := freeze missingFirstTree.2 firstRef.root firstRef.shape
  let ghostRows ← match build current saved
      (fun ref => if ref = firstRef then some partialRoot else registry ref)
      messages past query ⟨[0,0],none⟩ with
    | none => throw (IO.userError "captured unavailable cell rejected")
    | some a => pure a
  check "captured unavailable repeated cells remain explicitly unauthenticated ghost zeros"
    (ghostRows.rows == #[#[0],#[E.ofK 17],#[0]] &&
      ghostRows.selectedStatus == #[⟨false,false⟩,⟨true,true⟩,⟨false,false⟩])
  check "bad query lookup index rejects" (selectPhase 0 rootFrozen #[8]).isNone
  check "malformed stored geometry rejects"
    (lookup (fun _ => some {rootFrozen with raw := #[]}) firstRef).isNone
  check "malformed extension limb count rejects"
    (PCSBCSFrozenOracleRows.extensionOracle #[#[1,2]]).isNone
  check "noncanonical announced digest rejects"
    (build current saved registry messages past boundary ⟨[0,0,⟨0,0,1⟩,0],none⟩).isNone
  let otherTape := CausalProbability.set current tape (fun _ => ⟨99,98,97⟩,E.ofK 96)
  let otherPast := WHIRFiatShamir.Prefix.ofTape current otherTape
  let same ← match build current saved registry messages otherPast query ⟨[0,0],none⟩ with
    | none => throw (IO.userError "whole-current replacement rejected")
    | some a => pure a
  check "whole current query replacement leaves predecessor-derived rows unchanged"
    (same.rows == a.rows && same.queries == a.queries)
end Whir.PCSBCSSourceFrozenAccessorSmoke

def main : IO Unit := Whir.PCSBCSSourceFrozenAccessorSmoke.smoke
