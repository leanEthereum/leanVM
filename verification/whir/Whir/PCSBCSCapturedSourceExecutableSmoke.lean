import Whir.PCSBCSCapturedSourceExecutable
import Whir.PCSBCSSourceCallerOriginal
import Whir.PublicMerkleProgram

/-! Actual first-disclosure source construction on the lowest production
profile, with real BLAKE2s primitive Merkle records and the literal prepared
original caller. Construction-output fixture coins are explicit, not deployed
duplex outputs or an accepted PCS proof. Missing, future and malformed records
retain their actual capture/status behavior rather than granting honesty. -/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedSourceExecutableSmoke
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSCapturedSourceExecutable DuplexModeGame PublicMerkleLog

local instance : Add E := ⟨E.add⟩
local instance : Mul E := ⟨E.mul⟩
local instance : Zero E := ⟨E.zero⟩
local instance : One E := ⟨E.one⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

private def p : ParameterBounds.Profile := ⟨⟨0,by decide⟩,⟨0,by decide⟩⟩
private def layout : WHIRCallerClaims.CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩
private def Q : Nat := 2^20
private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val)%256,Nat.mod_lt _ (by decide)⟩
private def iv : Digest32 := digest 0

private def recordedTree (bad : Option Nat) : Nat → Nat → Digest32 × DuplexPublicSimulator.PublicLog
  | 0,start =>
    let words := (List.replicate 48 (if bad == some start then (9 : K) else 0)) ++
      ((List.range 16).map fun lane => UInt64.ofNat (10+start+lane))
    let bytes := ByteCodec.wordsBytes words
    PublicMerkleProgram.withHashStored blake2sOracle bytes (fun root =>
      (root,plan blake2sOracle bytes))
  | height+1,start =>
    let left := recordedTree bad height start
    let right := recordedTree bad height (start+2^height)
    let bytes := List.ofFn (ByteCodec.pairBytes (left.1,right.1))
    PublicMerkleProgram.withHashStored blake2sOracle bytes (fun root =>
      (root,left.2 ++ right.2 ++ plan blake2sOracle bytes))

private def savedFor (root : Digest32) : AnchoredHeaderCodec.Record :=
  ⟨AnchoredSourceCaller.shape layout,root,⟨digest 19,(fun _ => none),0,true,0,0⟩,
    E.ofK 3 :: List.replicate 14 0,E.ofK 23⟩
private def zeroToken : WHIRCallerShape.EventShape → WHIRCallerClaims.CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)
private def entryFor (saved : AnchoredHeaderCodec.Record) : FramedHistory :=
  WHIRCallerClaims.tokenHistory (digest 11) (digest 13)
    (((WHIRCallerClaims.callerShape layout).drop
      (WHIRCallerClaims.rootScalarCount layout)).map zeroToken ++
      (AnchoredHeaderCodec.openingScalars saved).map WHIRCallerClaims.CallerToken.sent)
private def boundary (saved : AnchoredHeaderCodec.Record) : Nat := (entryFor saved).frames.length
private def current (saved : AnchoredHeaderCodec.Record) :
    Option (EnteredPacket p Q iv (boundary saved)) :=
  let entry := entryFor saved
  if valid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f then
    if admitted : WHIRHistory.scheduledAdmissible (ParameterBounds.config p)
        [⟨[],none⟩] = true then
      if bounded : ∀ block : Fin (PCSBCSChallengeOracle.blocks
          (PCSBCSRounds.rawWidth (.initial : Coordinate (ParameterBounds.config p)))),
          DuplexFraming.pathCost (WHIRCallerPrefix.outputKeyFrom
            (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) entry [⟨[],none⟩] block.val) ≤ Q then
        some ⟨⟨entry,rfl⟩,⟨.initial,{
          messages := [⟨[],none⟩]
          nonempty := by decide
          admitted := admitted
          entryValid := valid
          position_eq := rfl
          pathBound := bounded}⟩⟩
      else none
    else none
  else none

private abbrev Keys (saved : AnchoredHeaderCodec.Record) :=
  PCSBCSSourceRootCapture.Key (p := p) (Q := Q) (iv := iv) (boundary := boundary saved)
private abbrev Answers (saved : AnchoredHeaderCodec.Record) :=
  PCSBCSSourceRootCapture.Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary saved)

private def primitiveKey (saved : AnchoredHeaderCodec.Record) (input : DuplexFraming.Node) : Keys saved :=
  .inr ⟨.inl input,by
    classical
    simp [EnteredPacket.partition,partitionOfInjection,EnteredPacket.encode]⟩

private def table (saved : AnchoredHeaderCodec.Record) (salt : Nat) : Table (Keys saved) (Answers saved)
  | .inl packet => fun block => digest (salt+block.val+position packet.2.coord)
  | .inr other => match other.val with
    | .inl input => blake2sOracle input
    | .inr _ => digest 0

private def ordinary (saved : AnchoredHeaderCodec.Record) {n : Nat}
    (log : DuplexPublicSimulator.PublicLog) (tail : Sampling (Keys saved) (Answers saved) Unit n) :
    Sampling (Keys saved) (Answers saved) Unit (log.length+n) :=
  match log with
  | [] => Sampling.pad (by simp) tail
  | record::rest => Sampling.pad (by simp only [List.length_cons]; omega)
      (.draw (primitiveKey saved record.1) (fun _ => ordinary saved rest tail))

private def addresses (saved : AnchoredHeaderCodec.Record) : Keys saved → List Reference
  | .inl _ => [⟨saved.root,initialShape saved.shape⟩]
  | .inr _ => []

private def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"captured source executable: {label}")
  IO.println s!"captured source executable PASS: {label}"

private def runSnapshot (saved : AnchoredHeaderCodec.Record)
    (cur : EnteredPacket p Q iv (boundary saved))
    (original : PCSBCSCallerBinding.CallerInput p) (before after : DuplexPublicSimulator.PublicLog)
    (salt : Nat) : Option (PCSBCSCallerBinding.CallerData p) :=
  let program := ordinary saved before
    (.draw (.inl cur) (fun _ => ordinary saved after (Sampling.ret (n := 0) ())))
  snapshotFromTable (addresses saved) ⟨saved.root,initialShape saved.shape⟩
    program original saved cur (table saved salt)

private def inspect (saved : AnchoredHeaderCodec.Record)
    (cur : EnteredPacket p Q iv (boundary saved)) (log : DuplexPublicSimulator.PublicLog) : Option Frozen :=
  let program := ordinary saved log (.draw (.inl cur) (fun _ => Sampling.ret (n := 0) ()))
  capture (addresses saved) ⟨saved.root,initialShape saved.shape⟩ program (table saved 0)

def smoke : IO Unit := do
  let shape := initialShape (savedFor (digest 17)).shape
  require "real lowest production geometry, full 64-word leaf and 16 occupied lanes"
    ((ParameterBounds.config p).logN == 15 && shape.height == 10 &&
      shape.leafWords == 64 && shape.occupied == 16)
  let tree := recordedTree none shape.height 0
  let saved := savedFor tree.1
  let cur ← match current saved with
    | none => throw (IO.userError "literal production source packet admission rejected")
    | some cur => pure cur
  let original ← match PCSBCSSourceCallerOriginal.original p layout saved (entryFor saved)
      (fun _ => digest 0) with
    | none => throw (IO.userError "actual original source constructor rejected")
    | some original => pure original
  require "packet has actual initial coordinate, complete source shape and immutable anchor"
    (position cur.2.coord == 0 && decide saved.Valid &&
      original.anchorValue == saved.value && original.anchorPoint == saved.point.toArray)
  let actual ← match runSnapshot saved cur original tree.2 [] 0 with
    | none => throw (IO.userError "actual first-mention source snapshot rejected")
    | some data => pure data
  require "captured native compact Root0 comes from real padded BLAKE2s images"
    (actual.observed.root.size == 1024 && actual.observed.root[0]!.size == 16 &&
      (actual.observed.root[0]!)[0]! == 10 && (actual.observed.root[3]!)[2]! == 15)
  require "whole source snapshot retains independent original and strict initial incoming trace"
    (actual.original.anchorPoint == original.anchorPoint && actual.original.anchorValue == original.anchorValue &&
      actual.original.m == original.m && actual.observed.trace.answers.isEmpty)
  let altered ← match runSnapshot saved cur original tree.2 [] 999 with
    | none => throw (IO.userError "changed whole current output rejected incoming snapshot")
    | some data => pure data
  require "changing all current raw output bytes cannot enter incoming Root0 or replies"
    (altered.observed.root == actual.observed.root && altered.observed.trace.answers.isEmpty &&
      altered.original.anchorPoint == actual.original.anchorPoint)
  let future ← match runSnapshot saved cur original [] tree.2 0 with
    | none => throw (IO.userError "actual ghost first capture rejected structural storage")
    | some data => pure data
  require "future primitive records do not retroactively populate the first captured Root0"
    (future.observed.root.size == 1024 && future.observed.root[0]!.size == 16 &&
      (future.observed.root[0]!)[0]! == 0 && (actual.observed.root[0]!)[0]! != 0)
  let noMention := ordinary saved tree.2 (Sampling.ret (n := 0) ())
  require "missing first mention rejects actual source constructor"
    (snapshotFromTable (addresses saved) ⟨saved.root,initialShape saved.shape⟩
      noMention original saved cur (table saved 0)).isNone
  require "disabled reference address does not become an authenticated zero table"
    (snapshotFromTable (fun _ => []) ⟨saved.root,initialShape saved.shape⟩
      (ordinary saved tree.2 (.draw (.inl cur) (fun _ => Sampling.ret (n := 0) ())))
      original saved cur (table saved 0)).isNone
  let malformed := recordedTree (some 3) shape.height 0
  let badSaved := savedFor malformed.1
  let badCur ← match current badSaved with
    | none => throw (IO.userError "bad-padding packet's syntax admission rejected")
    | some cur => pure cur
  let frozen ← match inspect badSaved badCur malformed.2 with
    | none => throw (IO.userError "actual malformed-image first capture missing")
    | some frozen => pure frozen
  require "genuinely hashed nonzero prefix remains available but padding-invalid"
    (frozen.cells[3]!.available && !frozen.cells[3]!.paddingValid &&
      frozen.cells[0]!.available && frozen.cells[0]!.paddingValid)
  IO.println s!"captured source executable PASS: physical BLAKE2s records {tree.2.length}"
end Whir.PCSBCSCapturedSourceExecutableSmoke

def main : IO Unit := Whir.PCSBCSCapturedSourceExecutableSmoke.smoke
