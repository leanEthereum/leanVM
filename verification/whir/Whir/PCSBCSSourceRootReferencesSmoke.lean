import Whir.PCSBCSSourceRootReferencesBudget

namespace Whir.PCSBCSSourceRootReferencesSmoke
open Whir Concrete Protocol FiatShamirGame WHIRHistory WHIRHistoryKey
open AnchoredHeaderCodec WHIRCallerClaims PCSBCSSourceRootReferences
open DuplexModeGame DuplexFraming PCSBCSMerkleRootCache

private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val) % 256,Nat.mod_lt _ (by decide)⟩
private def p : ParameterBounds.Profile := (⟨1,by decide⟩,⟨0,by decide⟩)
private def c : Config := ParameterBounds.config p
private def layout : CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 15,.committed (2^15) 0],⟨0,6,7⟩,1⟩
private def zeroToken : WHIRCallerShape.EventShape → CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)
private def compression : DuplexRefinement.Compression := compressionOf blake2sOracle
private def iv : Digest32 := DuplexCompression.parameterIV

private def pendingAt (n : Nat) : Pending :=
  let previous := ((schedule c)[n-1]?).getD .initial
  let q := ((schedule c)[n]?).getD .initial
  let scalars := if n = 0 then [] else
    match previous with
    | .fold i j =>
      if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then
        [0,0] ++ rootScalars (digest 17)
      else List.replicate (replyScalarCount previous) 0
    | _ => List.replicate (replyScalarCount previous) 0
  ⟨scalars,match q with | .query _ => some (0,0) | _ => none⟩
private def messages : List Pending := (List.range (depth c)).map pendingAt |>.reverse

private def require (label : String) (test : Bool) : IO Unit := do
  unless test do throw (IO.userError s!"root-reference smoke failed: {label}")
  IO.println s!"root-reference smoke: {label}"
private def describe (ref : Reference) : String :=
  s!"cv[0]={ref.root ⟨0,by decide⟩};height={ref.shape.height};image={ref.shape.leafWords};occupied={ref.shape.occupied}"
private def printParse (label : String) (result : Option Reference) : IO Unit :=
  IO.println s!"{label}: {result.map describe}"

def smoke : IO Unit := do
  let original := DuplexRefinement.seed compression iv (digest 7) (digest 9)
  let shape := AnchoredSourceCaller.shape layout
  let afterHeader := DuplexRefinement.absorb compression original
    (scalarBytes (headerScalars shape (digest 17)))
  let point ← match DuplexRefinement.sampleVec compression afterHeader shape.logN with
    | .ok (_,point) => pure point
    | .error _ => throw (IO.userError "original commitment anchor draw failed")
  let saved : Record := ⟨shape,digest 17,capture original,point,0⟩
  require "valid immutable original record" (decide saved.Valid)
  require "public PCS profile matches control shape" (decide (profileShape p saved.shape))
  require "production initial leaf retains padding and occupied suffix"
    (decide (saved.shape.lanes < (initialShape saved.shape).leafWords))
  let payload := ((WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout)).map zeroToken
  let tokens := payload ++ (openingScalars saved).map CallerToken.sent
  let entry := tokenHistory (digest 11) (digest 13) tokens
  let answers := DuplexRefinement.evalCoordinate compression iv
  require "fresh caller identity admitted" (AnchoredSourceFreshCaller.decode layout saved entry answers).isSome
  printParse "initial exact role3" (parseInitial saved (openingScalars saved) 3)
  printParse "initial rejected context-CV role5" (parseInitial saved (openingScalars saved) 5)
  require "wrong initial role rejected" (parseInitial saved (openingScalars saved) 5).isNone
  let foreign := {saved with value := saved.value+1}
  printParse "foreign immutable frame" (parseInitial saved (openingScalars foreign) 3)
  printParse "malformed immutable frame" (parseInitial saved ((openingScalars saved).drop 1) 3)
  require "foreign record rejected" (parseInitial saved (openingScalars foreign) 3).isNone
  require "malformed record rejected" (parseInitial saved ((openingScalars saved).drop 1) 3).isNone
  let arbitrary : Pending := ⟨rootScalars (digest 17),none⟩
  printParse "digest halves at non-root coordinate" (parsePhase c .initial arbitrary 1 0)
  require "no magic digest search across arbitrary scalar roles"
    (parsePhase c .initial arbitrary 1 0).isNone
  require "scheduled child-prefix admitted" (scheduledAdmissible c messages)
  let key := WHIRCallerPrefix.outputKeyFrom (stackWidth c) entry messages 0
  require "exact Pending parser roundtrip" (decide (parsePendingKey p entry key = some messages))
  let refs ← match parseReferences p layout saved entry answers key with
    | some refs => pure refs
    | none => throw (IO.userError "whole child key root parser rejected")
  IO.println s!"child-prefix exact parser: {refs.map describe}"
  require "multiple prior phase roots in ONE child key" (decide (2 ≤ (phaseReferences c messages).length))
  require "all references have repeated equal CV" (refs.all (fun ref => decide (ref.root = digest 17)))
  let announcements := PCSBCSSourceRootReferences.announcements [] refs
  let registry := registerAll ({} : Registry) announcements
  IO.println s!"ledger: source-key first-mention=1 references={refs.length} unique-shape-addresses={registry.size} complete-path-charge={pathCost key}"
  require "same CV is not registry deduplication key" (decide (2 ≤ registry.size))
  require "all references fit charged complete path" (decide (refs.length ≤ pathCost key))
  let repeated := registerAll registry announcements
  require "repeat exact addresses do not allocate" (decide (repeated.size = registry.size))
  let badKey := {key with history := {key.history with domain := digest 99}}
  require "foreign source seed rejected" (parsePendingKey p entry badKey).isNone
  require "foreign record binding rejected by whole parser"
    (parseReferences p layout foreign entry answers key).isNone
  for (m,n) in messages.reverse.zipIdx do
    if n > 0 then
      let q := ((schedule c)[n-1]?).getD .initial
      match q with
      | .fold i j =>
        if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then
          printParse "phase exact scalar2" (parsePhase c q m (i.val+1) 2)
          printParse "phase rejected scalar0" (parsePhase c q m (i.val+1) 0)
          printParse "phase rejected foreign index" (parsePhase c q m (i.val+2) 2)
          require "wrong phase offset rejected" (parsePhase c q m (i.val+1) 0).isNone
          require "wrong phase index rejected" (parsePhase c q m (i.val+2) 2).isNone
          let malformed : Pending := ⟨[0,0,⟨0,0,1⟩,0],m.nonce⟩
          printParse "phase rejected noncanonical root halves"
            (parsePhase c q malformed (i.val+1) 2)
          require "noncanonical root halves rejected"
            (parsePhase c q malformed (i.val+1) 2).isNone
      | _ => pure ()
  let physical := DuplexRefinement.evalCoordinate compression iv key
  IO.println s!"actual deployed compression output first byte={physical ⟨0,by decide⟩}"
  let final := register registry [] (digest 17) (initialShape saved.shape)
  require "final proof root already captured costs zero addresses" (decide (final.size = registry.size))

end Whir.PCSBCSSourceRootReferencesSmoke

def main : IO Unit := Whir.PCSBCSSourceRootReferencesSmoke.smoke
