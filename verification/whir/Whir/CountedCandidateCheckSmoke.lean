import Whir.ExtractorArithmeticCostPolynomial
import Whir.CountedCandidateCheckOriginalAnchor
import Whir.ExtractorArithmeticCostSource

/-! Bounded compiled smoke for the actual source encoder, full causal verifier, Root0 Gao decoder and all-claim checker. The legal reset machine retains its strict-prefix replay count. No intermediate GS backend is executed. -/
namespace Whir.CountedCandidateCheckSmoke
open SupportedCandidateExtraction
open Concrete Protocol CausalGame KnowledgeExtraction PCSRewindExtractor
open AuthenticatedResetSupport CountedCandidateCheck ExtractorArithmeticCost

def config : Config := ⟨3, #[1, 1], #[2, 2], #[16, 8], #[0, 1]⟩
def words : Array K := #[3, 5, 7, 11, 13, 17, 19, 23]
def tape : Tape config :=
  ⟨E.ofK 3, (fun _ => ⟨(fun _ => E.ofK 5), (fun _ _ => E.ofK 7),
    (fun _ => E.ofK 11), E.ofK 13⟩), (fun _ => E.ofK 17)⟩

def reply (proof : Opening) : Batch → Reply
  | .initial _ => .initial proof.initial
  | .fold level round _ =>
      .fold proof.levels[level]!.afterFold[round]!
        (if round + 1 = config.folds[level]! then proof.levels[level]!.nextOracle else none)
        (if level + 1 = config.folds.size && round + 1 = config.folds[level]! then proof.residual else #[])
  | .ood level index _ => .ood proof.levels[level]!.oods[index]!
  | .query level _ _ => .query proof.levels[level]!.rows proof.levels[level]!.intro
  | .tail round _ => .tail proof.tailMessages[round]!

def run : IO Unit := do
  let weight := tab 8 fun i => E.ofK (UInt64.ofNat (i + 29))
  let value := dot (words.map E.ofK) weight
  let (root, proof) ← match prove config (challenges config tape) words weight value with
    | .error message => throw (IO.userError message)
    | .ok result => pure result
  let input : Public := ⟨config, 2, root.map (Array.map E.c0), #[⟨weight, value⟩]⟩
  let strategy : Strategy := fun _ _ batch => reply proof batch
  let answers := CausalGame.run strategy input [] (visibleBatches config tape.1 (challenges config tape))
  let acceptance := countedAcceptedReplies input tape answers
  unless acceptance.1 == acceptedReplies input tape answers && acceptance.1 do
    throw (IO.userError "counted full verifier disagrees with actual accepted trial")
  let inverse := countedKinv 41
  unless inverse.1 == kinv 41 && inverse.2 == 127 do
    throw (IO.userError "source inverse value or 127-multiplication count mismatch")
  let encoded := countedEncode 2 2 #[E.ofK 3, E.ofK 5, E.ofK 7, E.ofK 11]
  unless encoded.1 == encode 2 2 #[E.ofK 3, E.ofK 5, E.ofK 7, E.ofK 11] do
    throw (IO.userError "counted source encoder mismatch")
  let originalPoint := #[E.ofK 29, E.ofK 31, E.ofK 37]
  let equality := countedOriginalEqWeight originalPoint 5
  unless equality.1 == RingPCSGame.eqWeight originalPoint 5 && equality.2 == 4 do
    throw (IO.userError "original equality-factor bit/lookup arithmetic mismatch")
  let strided := RingPCSGame.PointClaim.strided 4 1 1 #[E.ofK 3, E.ofK 5] 0
  let located := countedOriginalPointWeight strided 9
  let outside := countedOriginalPointWeight strided 8
  unless located.1 == RingPCSGame.pointWeight strided 9 && located.2 == 3 &&
      outside.1 == 0 && outside.2 == 0 do
    throw (IO.userError "literal original strided selector or field count mismatch")
  let anchorCheck := countedOriginalMle (words.map E.ofK) originalPoint
  unless anchorCheck.1 == Concrete.mle (words.map E.ofK) originalPoint && anchorCheck.2 == 37 do
    throw (IO.userError "literal retained anchor arithmetic mismatch")
  let level : Fin input.config.folds.size := ⟨0, by change 0 < config.folds.size; decide⟩
  let noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64 := by
    change 4 ≤ 64
    decide
  let program := countedCollect input level 4 [tape] 0 (fun records total =>
    let decoded := countedDecodeAndCheck input (baseRecords records) noWrap
    .finish decoded.1 (total + decoded.2))
  let fuel := collectionFuel input [tape]
  let result := runCounted input strategy (streamLength config) fuel program
  let actual := runRewind input strategy (streamLength config) fuel program.erase
  unless result.output.map (fun witness => Array.ofFn witness) == some words do
    throw (IO.userError "counted legal extractor did not recover the literal K witness")
  unless result.output.map (fun witness => Array.ofFn witness) ==
      actual.output.map (fun witness => Array.ofFn witness) && result.responseCalls == actual.responseCalls do
    throw (IO.userError "counted legal machine disagrees with existing rewind interpreter")
  let records := baseRecords (acceptedRecords input tape level 4 answers)
  let received := countedReceivedTables input records
  unless received.1 == Array.ofFn (fun lane : Fin input.lanes =>
      Array.ofFn (fun q : Fin (blockLength input.config) => receivedLane input records lane q)) &&
      received.2 ≤ blockLength input.config * records.length + input.lanes * blockLength input.config do
    throw (IO.userError "counted lookup/received-row loop value or bound mismatch")
  let matched := countedCommonCoordinates input.config input.lanes (words.map E.ofK) records
  unless decide (matched.1 =
      SupportedCandidateExtraction.commonCoordinates input.config input.lanes (words.map E.ofK) records) &&
      matched.2 ≤ records.length * (1 + 3 * input.lanes) + records.length * (records.length + 1) do
    throw (IO.userError "counted common-coordinate comparison value or bound mismatch")
  let checked := countedDecodeAndCheck input records noWrap
  let original := decodeAndCheck input records noWrap
  unless checked.1.map (fun witness => Array.ofFn witness) ==
      original.1.map (fun witness => Array.ofFn witness) do
    throw (IO.userError "counted decode/check disagrees with actual output")
  unless checked.2 ≤ decodeCheckBound input && acceptance.2 > 0 && checked.2 > original.2 do
    throw (IO.userError "full arithmetic counter omitted verifier or candidate-check work")
  unless decide (ParameterBounds.threshold input.config 0 ≤
      (SupportedCandidateExtraction.commonCoordinates input.config input.lanes (words.map E.ofK) records).card) do
    throw (IO.userError "false-claim fixture lacks enough authenticated common coordinates")
  let falseInput : Public := ⟨config, 2, input.root, #[⟨weight, value + E.ofK 1⟩]⟩
  let falseCheck := countedDecodeAndCheck falseInput records noWrap
  unless falseCheck.1.isNone do throw (IO.userError "original public false claim was not checked")
  let malformed : Strategy := fun _ _ _ => .tail default
  let rejected := runCounted input malformed (streamLength config) fuel program
  unless rejected.output.isNone do throw (IO.userError "malformed causal replies were accepted")
  let witness : Witness config 2 := fun i => words[i.val]!
  let familyWeights := tab 8 (RingPCSGame.regionWeight 0 originalPoint)
  let families : Fin 1 → RingPCSGame.FamilyClaim := fun _ =>
    ⟨0, originalPoint, fun bit => OriginalClaimsChecker.slice words familyWeights bit⟩
  let pointPrototype := RingPCSGame.PointClaim.strided 4 1 1 #[E.ofK 3] 0
  let pointValue := dot (words.map E.ofK) (RingPCSGame.publicPoint 8 pointPrototype).weight
  let originalPoints := #[RingPCSGame.PointClaim.strided 4 1 1 #[E.ofK 3] pointValue]
  let anchorValue := Concrete.mle (words.map E.ofK) originalPoint
  let prepared ← match (OriginalClaimsChecker.countedPrepare config 2 families originalPoints originalPoint anchorValue).1 with
    | none => throw (IO.userError "guarded original family/strided/anchor preparation rejected")
    | some prepared => pure prepared
  let preparation := (OriginalClaimsChecker.countedPrepare config 2 families originalPoints originalPoint anchorValue).2
  let originalCheck := OriginalClaimsChecker.countedCheck prepared witness
  unless originalCheck.1 == OriginalClaimsChecker.check prepared witness && originalCheck.1 &&
      originalCheck.2.fieldArithmetic == 54 && preparation.fieldArithmetic == 124 do
    throw (IO.userError "all64 original slices, strided point or saved anchor counter disagrees")
  let mapDraws : Fin 6 → E := fun j => if j.val == 0 then 1 else 0
  let publicPrefix : RingPCSGame.Prefix := ⟨1, mapDraws⟩
  let mapped := OriginalClaimsChecker.countedMap mapDraws (E.ofK 41)
  unless mapped.1 == RingPCSGame.executableMap mapDraws (E.ofK 41) && mapped.2 == 75 do
    throw (IO.userError "actual 63-square/six-scale/six-add public map disagrees")
  let originalPublic := OriginalClaimsChecker.countedInput prepared #[] publicPrefix
  unless originalPublic.2.fieldArithmetic == 5673 do
    throw (IO.userError "cached original source public transformation count disagrees")
  let sourceStatement := batchClaims 8 originalPublic.1.claims tape.1
  let (sourceRoot, sourceProof) ← match prove config (challenges config tape) words sourceStatement.weight sourceStatement.value with
    | .error message => throw (IO.userError message)
    | .ok result => pure result
  let sourceInput := OriginalClaimsChecker.input prepared (sourceRoot.map (Array.map E.c0)) publicPrefix
  let sourceStrategy : Strategy := fun _ _ batch => reply sourceProof batch
  let sourceLevel : Fin sourceInput.config.folds.size := ⟨0, by change 0 < config.folds.size; decide⟩
  let sourceNoWrap : sourceInput.config.logN - sourceInput.config.folds[0]! + sourceInput.config.rates[0]! ≤ 64 := by
    change 4 ≤ 64
    decide
  let sourceProgram := ExtractorArithmeticCostSource.program sourceInput sourceLevel [tape] sourceNoWrap
    (OriginalClaimsChecker.countedCheck prepared)
  let sourceFuel := collectionFuel sourceInput [tape]
  let sourceMeasured := runCounted sourceInput sourceStrategy (streamLength config) sourceFuel sourceProgram
  let sourceActual := runRewind sourceInput sourceStrategy (streamLength config) sourceFuel
    (PCSRewindSource.program sourceInput sourceLevel [tape] sourceNoWrap (OriginalClaimsChecker.check prepared))
  unless sourceMeasured.output.map (fun w => Array.ofFn w) == some words &&
      sourceMeasured.output.map (fun w => Array.ofFn w) == sourceActual.output.map (fun w => Array.ofFn w) &&
      sourceMeasured.responseCalls == sourceActual.responseCalls do
    throw (IO.userError "counted actual original-source legal reset/Root0 result or replay calls disagree")
  let lyingFamilies : Fin 1 → RingPCSGame.FamilyClaim := fun j =>
    {families j with slices := fun bit => (families j).slices bit + if bit.val == 0 then 1 else 0}
  let lyingPrepared ← match OriginalClaimsChecker.prepare config 2 lyingFamilies originalPoints originalPoint anchorValue with
    | none => throw (IO.userError "well-shaped false original family failed metadata guard")
    | some prepared => pure prepared
  let lyingInput := OriginalClaimsChecker.input lyingPrepared sourceInput.root publicPrefix
  unless lyingInput.claims.map (fun claim => (claim.weight, claim.value)) ==
      sourceInput.claims.map (fun claim => (claim.weight, claim.value)) do
    throw (IO.userError "source map kernel did not mask the false uncompressed slice")
  let sourceAnswers := CausalGame.run sourceStrategy sourceInput [] (visibleBatches config tape.1 (challenges config tape))
  let sourceRecords := baseRecords (acceptedRecords sourceInput tape sourceLevel 4 sourceAnswers)
  unless decide (ParameterBounds.threshold config 0 ≤
      (SupportedCandidateExtraction.commonCoordinates config 2 (words.map E.ofK) sourceRecords).card) do
    throw (IO.userError "false original-family fixture lacks enough authenticated records")
  let compressedOnly := countedDecodeAndCheck lyingInput sourceRecords sourceNoWrap
  unless compressedOnly.1.isSome do
    throw (IO.userError "masked false-family fixture did not pass the compressed public checker")
  let lyingMeasured := runCounted lyingInput sourceStrategy (streamLength config) sourceFuel
    (ExtractorArithmeticCostSource.program lyingInput sourceLevel [tape] sourceNoWrap
      (OriginalClaimsChecker.countedCheck lyingPrepared))
  let lyingActual := runRewind lyingInput sourceStrategy (streamLength config) sourceFuel
    (PCSRewindSource.program lyingInput sourceLevel [tape] sourceNoWrap (OriginalClaimsChecker.check lyingPrepared))
  unless lyingMeasured.output.isNone && lyingActual.output.isNone &&
      lyingMeasured.responseCalls == lyingActual.responseCalls do
    throw (IO.userError "actual uncompressed all64 original checker accepted a masked false family")
  let malformedFamilies : Fin 1 → RingPCSGame.FamilyClaim := fun j => {families j with offset := 8}
  unless (OriginalClaimsChecker.countedPrepare config 2 malformedFamilies originalPoints originalPoint anchorValue).1.isNone &&
      (OriginalClaimsChecker.countedPrepare config 2 families originalPoints #[E.ofK 29] anchorValue).1.isNone do
    throw (IO.userError "literal original span or saved-anchor dimension guard was bypassed")
  IO.println s!"counted-original-source: prepare-field={preparation.fieldArithmetic}, public-field={originalPublic.2.fieldArithmetic}, all64+strided+anchor-field={originalCheck.2.fieldArithmetic}, map-field={mapped.2}"
  IO.println s!"counted-original-resources: prepare={preparation.total}, public={originalPublic.2.total}, all64-check={originalCheck.2.total}, bit-reads={originalCheck.2.bitReads}"
  IO.println s!"counted-original-source-root0: field={sourceMeasured.fieldArithmetic + preparation.fieldArithmetic + originalPublic.2.fieldArithmetic}, replay-calls={sourceMeasured.responseCalls}, reply-words={sourceMeasured.encodedReplyWords}; masked false original rejected after enough authenticated records"
  IO.println s!"counted-source: inverse={inverse.2}, encoder={encoded.2}, verifier={acceptance.2}"
  IO.println s!"counted-root0: decoder={original.2}, decode+allclaims={checked.2}, total={result.fieldArithmetic}, replay-calls={result.responseCalls}, reply-words={result.encodedReplyWords}"
  IO.println s!"counted-loops: received={received.2}, common-comparisons={matched.2}, admitted-public-and-record-words={consumedWords input records}"
  IO.println s!"counted-original-primitives: equality={equality.2}, strided={located.2}, anchor-mle={anchorCheck.2}"
  IO.println "counted-root0: exact source/check/reset result agreement; false claim checked after enough authenticated records; malformed replies rejected"

end Whir.CountedCandidateCheckSmoke

def main : IO Unit := Whir.CountedCandidateCheckSmoke.run
