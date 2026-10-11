import Whir.AnchoredSourceFreshCaller
import Lean.Util.CollectAxioms

/-! Standalone executable fresh-caller parser regression. Real deployed primitive
outputs are recovered in two different transcript seeds. Payload scalar zeroes
are claim-projection fixture data, not an honest algebraically verified caller
proof; no packet/native-verifier or concrete hash-security claim follows. -/
namespace Whir.AnchoredSourceFreshCallerSmoke
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

private def compression : DuplexRefinement.Compression :=
  DuplexModeGame.compressionOf DuplexModeGame.blake2sOracle
private def iv : Digest32 := DuplexCompression.parameterIV
/-- The existing exact byte formula avoids evaluating the recursive encoder's
high-index Fin eliminators repeatedly in this compiled fixture. -/
private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val) % 256,Nat.mod_lt _ (by decide)⟩

private theorem digest_exact (n : Nat) : digest n = ByteCodec.encodeNat 32 n := by
  funext i
  apply Fin.ext
  exact (ByteCodec.encodeNat_byte 32 n i).symm
private def layout : CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩

private def zeroToken : WHIRCallerShape.EventShape → CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)

private def payloadTokens : List CallerToken :=
  ((WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout)).map zeroToken

private def boundTokens (saved : Record) : List CallerToken :=
  payloadTokens ++ (openingScalars saved).map CallerToken.sent

private def freshEntry (tokens : List CallerToken) : FramedHistory :=
  tokenHistory (digest 11) (digest 13) tokens

/-- Store each permitted physical output as bytes once. Outside-output answers
are irrelevant to `entryTokens`, exactly as in its existing observer contract. -/
private def actualBlocks (entry : FramedHistory) : List (Coordinate × Array Byte) :=
  (WHIRCallerOutputs.callerOutputs entry).map
    (fun q => (q,Array.ofFn (DuplexRefinement.evalCoordinate compression iv q)))

private def answersFromBlocks (blocks : List (Coordinate × Array Byte)) (q : Coordinate) : Digest32 :=
  match blocks.find? (fun row => decide (row.1 = q)) with
  | some (_,bytes) => fun i => bytes[i.val]!
  | none => digest 0

private theorem actualAnswers_observed (entry : FramedHistory) (q : Coordinate)
    (member : q ∈ WHIRCallerOutputs.callerOutputs entry) :
    answersFromBlocks (actualBlocks entry) q = DuplexRefinement.evalCoordinate compression iv q := by
  unfold answersFromBlocks actualBlocks
  let blocks := (WHIRCallerOutputs.callerOutputs entry).map
    (fun q => (q,Array.ofFn (DuplexRefinement.evalCoordinate compression iv q)))
  change (match blocks.find? (fun row => decide (row.1 = q)) with
    | some (_,bytes) => fun (i : Fin 32) => bytes[i.val]!
    | none => digest 0) = _
  cases found : blocks.find? (fun row => decide (row.1 = q)) with
  | none =>
    have absent := List.find?_eq_none.mp found
    have contained : (q,Array.ofFn (DuplexRefinement.evalCoordinate compression iv q)) ∈ blocks :=
      List.mem_map.mpr ⟨q,member,rfl⟩
    have impossible := absent _ contained
    simp at impossible
  | some row =>
    obtain ⟨key,_,equal⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
    have predicate := List.find?_some found
    have keyEq : row.1 = q := of_decide_eq_true predicate
    subst row
    dsimp only at keyEq
    subst key
    funext i
    simp

private theorem fresh_actual (saved : Record) (entry : FramedHistory) :
    AnchoredSourceFreshCaller.decode layout saved entry (answersFromBlocks (actualBlocks entry)) =
      AnchoredSourceFreshCaller.physical compression iv layout saved entry :=
  AnchoredSourceFreshCaller.decode_physical compression iv layout saved entry
    (answersFromBlocks (actualBlocks entry)) (actualAnswers_observed entry)

private def parseFresh (saved : Record) (tokens : List CallerToken) :
    Option AnchoredSourceCaller.Claims :=
  let entry := freshEntry tokens
  let blocks := actualBlocks entry
  AnchoredSourceFreshCaller.decode layout saved entry (answersFromBlocks blocks)

private def changedFrame (saved : Record) : Record :=
  {saved with value := saved.value+1}

private def require (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"fresh-caller parser smoke failed: {label}")
  IO.println s!"fresh-caller parser: {label}"

/-- Obtain the saved anchor from the original seeded stream, then parse a
separately seeded fresh payload with no original header or anchor draw. -/
def smoke : IO Unit := do
  IO.println "fresh-caller parser: starting actual original/fresh fixture"
  let original := DuplexRefinement.seed compression iv (digest 7) (digest 9)
  let shape := AnchoredSourceCaller.shape layout
  let root := digest 17
  let header := headerScalars shape root
  let afterHeader := DuplexRefinement.absorb compression original (WHIRHistory.scalarBytes header)
  let point ← match DuplexRefinement.sampleVec compression afterHeader shape.logN with
    | .ok (_,point) => pure point
    | .error _ => throw (IO.userError "original anchor sampling failed")
  require "original physical anchor derived" (point.length == shape.logN)
  let saved : Record := ⟨shape,root,capture original,point,E.ofK 23⟩
  require "trusted saved record metadata valid" (decide saved.Valid)
  let tokens := boundTokens saved
  let originalTokens := header.map CallerToken.sent ++ point.map CallerToken.draw ++
    [CallerToken.sent saved.value] ++ tokens
  let originalEntry := tokenHistory (digest 7) (digest 9) originalTokens
  let entry := freshEntry tokens
  require "genuinely separate transcript seed" (decide (originalEntry.domain ≠ entry.domain))
  let originalBlocks := actualBlocks originalEntry
  let originalClaims := AnchoredSourceCaller.decode layout saved.context originalEntry (answersFromBlocks originalBlocks)
  require "original record parsed before saving" (match originalClaims with
    | some decoded => decide (decoded.record = saved ∧ decoded.caller.root = root)
    | none => false)
  let claims := parseFresh saved tokens
  require "fresh saved-record payload accepted" (match claims with
    | some decoded => decide (decoded.record = saved ∧ decoded.caller.root = root)
    | none => false)
  require "changed frame retains exact fresh shape" (decide
    (tokensShape (boundTokens (changedFrame saved)) = AnchoredSourceFreshCaller.callerShape layout saved))
  require "changed binding frame rejected" (parseFresh saved (boundTokens (changedFrame saved))).isNone
  let insertedHeader := header.map CallerToken.sent ++ tokens
  require "inserted original header rejected" (parseFresh saved insertedHeader).isNone
  let resampled := payloadTokens ++ point.map CallerToken.draw ++
    (openingScalars saved).map CallerToken.sent
  require "resampled anchor rejected" (parseFresh saved resampled).isNone
  let leftovers := tokens ++ [.sent 0]
  require "leftover scalar rejected" (parseFresh saved leftovers).isNone
  let leftoverEntry := freshEntry leftovers
  let leftoverBlocks := actualBlocks leftoverEntry
  let leftoverRaw := (WHIRCallerClaims.entryTokens leftoverEntry (answersFromBlocks leftoverBlocks)).bind
    (AnchoredSourceFreshCaller.sourceClaims layout saved)
  require "state parser retains leftover before exact guard" (match leftoverRaw with
    | some (decoded,rest) => decide (decoded.record = saved ∧ rest = [.sent 0])
    | none => false)
  let broken := {entry with frames := entry.frames.mapIdx (fun i frame =>
    if i = 0 then
      match frame with
      | .absorb consumed bytes => .absorb (consumed+1) bytes
      | .nonce consumed bits nonce => .nonce (consumed+1) bits nonce
    else frame)}
  let malformedBlocks := actualBlocks broken
  let malformed := AnchoredSourceFreshCaller.decode layout saved broken (answersFromBlocks malformedBlocks)
  require "malformed consumption cursor rejected" malformed.isNone

#print axioms AnchoredSourceFreshCaller.decode_physical
#print axioms AnchoredSourceFreshCaller.interpret_exact
#print axioms AnchoredSourceFreshCaller.decode_retained
#print axioms AnchoredSourceFreshCaller.decode_geometry
#print axioms AnchoredSourceFreshCaller.decode_nativeShapes
#print axioms AnchoredSourceFreshCaller.decode_anchored_shapes
#print axioms AnchoredSourceFreshCaller.binding_frame_rejected
#print axioms AnchoredSourceFreshCaller.sourceClaims_bound
#print axioms digest_exact
#print axioms actualAnswers_observed
#print axioms fresh_actual

end Whir.AnchoredSourceFreshCallerSmoke

def main : IO Unit := Whir.AnchoredSourceFreshCallerSmoke.smoke
