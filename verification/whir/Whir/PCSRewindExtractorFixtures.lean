import Whir.PCSRewindExtractor
import Whir.PCSRewindSourceProgram

/-! Dense-model Root0 program smoke with eight nonzero K coefficients, all
original family slices, ordinary/strided points, and the retained anchor.
A false second family masked by gamma=0 must fail the real original checker.
This tests the legal collector/decoder/checker, not the physical header/byte adapter.
The independent extension GS artifact is neither imported nor run here. -/
namespace Whir.PCSRewindExtractorFixtures
open Concrete Protocol CausalGame PCSRewindExtractor KnowledgeExtraction

def sourceConfig : Config := ⟨3, #[1, 1], #[2, 2], #[16, 8], #[0, 1]⟩
def sourceWords : Array K := #[3, 5, 7, 11, 13, 17, 19, 23]
def sourceTape : Tape sourceConfig :=
  ⟨E.ofK 3, (fun _ => ⟨(fun _ => E.ofK 5), (fun _ _ => E.ofK 7),
    (fun _ => E.ofK 11), E.ofK 13⟩), (fun _ => E.ofK 17)⟩

def replyOfOpening (c : Config) (proof : Opening) : Batch → Reply
  | .initial _ => .initial proof.initial
  | .fold level round _ =>
      .fold proof.levels[level]!.afterFold[round]!
        (if round + 1 = c.folds[level]! then proof.levels[level]!.nextOracle else none)
        (if level + 1 = c.folds.size && round + 1 = c.folds[level]! then proof.residual else #[])
  | .ood level index _ => .ood proof.levels[level]!.oods[index]!
  | .query level _ _ => .query proof.levels[level]!.rows proof.levels[level]!.intro
  | .tail round _ => .tail proof.tailMessages[round]!

def sourceStrategy (c : Config) (proof : Opening) : Strategy := fun _ _ batch => replyOfOpening c proof batch

def runSource : IO Unit := do
  let weight := tab 8 fun i => E.ofK (UInt64.ofNat (i + 29))
  let claim := dot (sourceWords.map E.ofK) weight
  let anchorPoint : Array E := #[E.ofK 41, E.ofK 43, E.ofK 47]
  let anchorWeight := eqTable anchorPoint
  let anchorValue := Concrete.mle (sourceWords.map E.ofK) anchorPoint
  let originalClaims : Array Claim := #[⟨weight, claim⟩, ⟨anchorWeight, anchorValue⟩]
  let statement := batchClaims 8 originalClaims sourceTape.1
  unless statement.value == claim + sourceTape.1 * anchorValue do
    throw (IO.userError "retained anchor lost its final lambda power")
  let (root, proof) ← match prove sourceConfig (challenges sourceConfig sourceTape)
      sourceWords statement.weight statement.value with
    | .error message => throw (IO.userError message)
    | .ok result => pure result
  let input : Public := ⟨sourceConfig, 2, root.map (Array.map E.c0), originalClaims⟩
  let tapes : List (Tape input.config) := [sourceTape]
  let strategy := sourceStrategy sourceConfig proof
  unless experiment input strategy sourceTape do throw (IO.userError "source trial rejected")
  let program := extractionProgram input ⟨0, by change 0 < sourceConfig.folds.size; decide⟩ tapes
    (by change 4 ≤ 64; decide)
  let result := runRewind input strategy (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel input tapes) program
  let recovered := result.output.map (fun w => Array.ofFn w)
  unless recovered == some sourceWords do throw (IO.userError "whole source witness mismatch")
  unless input.claims.all (fun original =>
      dot (recovered.getD #[] |>.map E.ofK) original.weight == original.value) do
    throw (IO.userError "extracted witness does not explain every original claim")
  unless Concrete.mle (recovered.getD #[] |>.map E.ofK) anchorPoint == anchorValue do
    throw (IO.userError "extracted witness changed the retained original anchor")
  IO.println s!"whole-source: {sourceWords.size} nontrivial K coefficients, calls={result.responseCalls}"
  let malformed : Strategy := fun _ _ _ => .tail default
  let malformedResult := runRewind input malformed (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel input tapes) program
  unless malformedResult.output.isNone do throw (IO.userError "malformed reply accepted by extractor")
  let adverse : Strategy := fun instanceInput past batch =>
    match batch with
    | .query level squeezes lambda =>
        match strategy instanceInput past (.query level squeezes lambda) with
        | .query rows intro => .query (rows.map (fun row => row.map (fun e => e + E.ofK 1))) intro
        | other => other
    | other => strategy instanceInput past other
  let adverseResult := runRewind input adverse (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel input tapes) program
  unless adverseResult.output.isNone do throw (IO.userError "unauthenticated adverse row accepted")
  unless !(experiment input adverse sourceTape) do
    throw (IO.userError "unauthenticated adverse trial accepted")
  let withholding : Strategy := fun instanceInput past batch =>
    match batch with
    | .query _ _ _ => .query #[] default
    | other => strategy instanceInput past other
  unless !(experiment input withholding sourceTape) do
    throw (IO.userError "withholding trial accepted")
  let withholdingResult := runRewind input withholding (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel input tapes) program
  unless withholdingResult.output.isNone do
    throw (IO.userError "withholding prover produced extracted output")
  let wrongInput : Public := { input with claims := #[⟨weight, claim + E.ofK 1⟩] }
  unless !(experiment wrongInput strategy sourceTape) do
    throw (IO.userError "wrong original claim accepted")
  let wrongProgram := extractionProgram wrongInput
    ⟨0, by change 0 < sourceConfig.folds.size; decide⟩ [sourceTape] (by change 4 ≤ 64; decide)
  let wrongResult := runRewind wrongInput strategy (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel wrongInput [sourceTape]) wrongProgram
  unless wrongResult.output.isNone do
    throw (IO.userError "wrong original claim produced extracted output")
  IO.println "whole-source: every original claim agrees; withholding and wrong claim rejected"
  IO.println "whole-source: malformed tags and adverse rows rejected"
  let zeroLambdaTape := CausalProbability.set (.query ⟨0, by decide⟩) sourceTape
    ⟨(fun _ => E.ofK 11), E.zero⟩
  let (honestRoot, honestProof) ← match prove sourceConfig (challenges sourceConfig zeroLambdaTape)
      sourceWords statement.weight statement.value with
    | .error message => throw (IO.userError message)
    | .ok result => pure result
  let changedRow := (honestRoot[1]!).map (fun e => e + E.ofK 1)
  let changedRoot := honestRoot.set! 1 changedRow
  let changedRows := (honestProof.levels[0]!).rows.set! 1 changedRow
  let changedFirst := { (honestProof.levels[0]!) with rows := changedRows }
  let changedProof := {honestProof with levels := honestProof.levels.set! 0 changedFirst}
  let changedInput : Public := ⟨sourceConfig, 2, changedRoot.map (Array.map E.c0), originalClaims⟩
  let changedStrategy := sourceStrategy sourceConfig changedProof
  unless experiment changedInput changedStrategy zeroLambdaTape do
    throw (IO.userError "malformed committed word should accept this legal trial")
  let changedTapes : List (Tape changedInput.config) := [zeroLambdaTape]
  let changedProgram := extractionProgram changedInput
    ⟨0, by change 0 < sourceConfig.folds.size; decide⟩ changedTapes (by change 4 ≤ 64; decide)
  let changedResult := runRewind changedInput changedStrategy (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel changedInput changedTapes) changedProgram
  unless changedResult.output.map (fun w => Array.ofFn w) == some sourceWords do
    throw (IO.userError "malformed committed word lost its nearby supported witness")
  IO.println "whole-source: accepted malformed commitment, nearby witness recovered without honest-root equality"
  -- Gamma=0 suppresses the SECOND original family in the compressed claim.
  -- The actual source checker must nevertheless reject its incorrect slice.
  let witness : Witness sourceConfig 2 := fun i => sourceWords[i.val]!
  let skeleton : Fin 2 → RingPCSGame.FamilyClaim := fun i =>
    ⟨0, if i.val = 0 then #[E.ofK 2, E.ofK 3, E.ofK 5] else #[E.ofK 7, E.ofK 11, E.ofK 13],
      fun _ => 0⟩
  let slices := RingPCSGame.honestSlices sourceConfig 2 skeleton witness
  let families : Fin 2 → RingPCSGame.FamilyClaim := fun i => {skeleton i with slices := slices i}
  let lyingFamilies : Fin 2 → RingPCSGame.FamilyClaim := fun i =>
    {families i with slices := fun bit =>
      if i.val = 1 ∧ bit.val = 0 then (families i).slices bit + 1 else (families i).slices bit}
  let ordinaryPoint : Array E := #[E.ofK 29, E.ofK 31, E.ofK 37]
  let stridedPoint : Array E := #[E.ofK 43, E.ofK 47]
  let stridedWords := #[sourceWords[1]!, sourceWords[3]!, sourceWords[5]!, sourceWords[7]!]
  let sourcePoints : Array RingPCSGame.PointClaim :=
    #[.point 0 ordinaryPoint (Concrete.mle (sourceWords.map E.ofK) ordinaryPoint),
      .strided 0 1 1 stridedPoint (Concrete.mle (stridedWords.map E.ofK) stridedPoint)]
  let honestPrepared ← match OriginalClaimsChecker.prepare sourceConfig 2 families sourcePoints anchorPoint anchorValue with
    | none => throw (IO.userError "honest source public cache rejected")
    | some prepared => pure prepared
  let lyingPrepared ← match OriginalClaimsChecker.prepare sourceConfig 2 lyingFamilies sourcePoints anchorPoint anchorValue with
    | none => throw (IO.userError "wrong family is well-shaped but cache rejected it")
    | some prepared => pure prepared
  let publicPrefix : RingPCSGame.Prefix := ⟨0, fun _ => 0⟩
  let skeletonInput := OriginalClaimsChecker.input honestPrepared #[] publicPrefix
  let sourceStatement := batchClaims 8 skeletonInput.claims sourceTape.1
  let (sourceRoot, sourceProof) ← match prove sourceConfig (challenges sourceConfig sourceTape)
      sourceWords sourceStatement.weight sourceStatement.value with
    | .error message => throw (IO.userError message)
    | .ok result => pure result
  let sourceBaseRoot := sourceRoot.map (Array.map E.c0)
  let honestInput := OriginalClaimsChecker.input honestPrepared sourceBaseRoot publicPrefix
  let lyingInput := OriginalClaimsChecker.input lyingPrepared sourceBaseRoot publicPrefix
  unless honestInput.claims.map (fun claim => (claim.weight, claim.value)) ==
      lyingInput.claims.map (fun claim => (claim.weight, claim.value)) do
    throw (IO.userError "gamma=0 did not mask the second family's false original slice")
  let sourceProver := sourceStrategy sourceConfig sourceProof
  unless experiment honestInput sourceProver sourceTape && experiment lyingInput sourceProver sourceTape do
    throw (IO.userError "source compressed protocol regression did not accept both inputs")
  let sourceLevel : Fin sourceConfig.folds.size := ⟨0, by decide⟩
  let sourceNoWrap : sourceConfig.logN - sourceConfig.folds[0]! + sourceConfig.rates[0]! ≤ 64 := by decide
  let sourceTapes : List (Tape sourceConfig) := [sourceTape]
  let genericResult := runRewind lyingInput sourceProver (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel lyingInput sourceTapes)
    (extractionProgram lyingInput sourceLevel sourceTapes sourceNoWrap)
  unless genericResult.output.map (fun w => Array.ofFn w) == some sourceWords do
    throw (IO.userError "compressed generic regression failed to recover the supported word")
  let honestResult := runRewind honestInput sourceProver (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel honestInput sourceTapes)
    (PCSRewindSource.program honestInput sourceLevel sourceTapes sourceNoWrap
      (OriginalClaimsChecker.check honestPrepared))
  let lyingResult := runRewind lyingInput sourceProver (streamLength sourceConfig)
    (AuthenticatedResetSupport.collectionFuel lyingInput sourceTapes)
    (PCSRewindSource.program lyingInput sourceLevel sourceTapes sourceNoWrap
      (OriginalClaimsChecker.check lyingPrepared))
  unless honestResult.output.map (fun w => Array.ofFn w) == some sourceWords do
    throw (IO.userError "actual original source checker rejected its honest supported word")
  unless lyingResult.output.isNone do
    throw (IO.userError "actual source checker accepted a gamma-masked false original family")
  IO.println s!"original-source: two full families, ordinary/strided points and retained anchor agree; calls={honestResult.responseCalls}"
  IO.println s!"original-source: gamma=0 generic/compressed accepts, uncompressed false second family rejects; calls={lyingResult.responseCalls}"


end Whir.PCSRewindExtractorFixtures

/-- Run the actual Root0 extractor on a small nontrivial legal source instance. -/
def main : IO Unit := Whir.PCSRewindExtractorFixtures.runSource
