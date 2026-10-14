import Whir.ExtractorArithmeticCostVerifierTotal

/-! Complete Root0 Gao plus candidate checking, executed inside the legal strict-prefix reset machine. The field counter is accumulated only when an actual full verifier trial or decode/check runs. Black-box response calls are separate oracle accesses; external prover time and arbitrary reply allocation are not claimed to be extractor field arithmetic. -/
namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck

/-- The existing decoder is Root0 Gao only. Its counted field arithmetic is combined with the full cached common-coordinate and original-claims check. -/
def countedDecodeAndCheck (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    Option (Witness input.config input.lanes) × Nat :=
  let decoded := decodeRecords input records noWrap
  match decoded.1 with
  | none => (none, decoded.2)
  | some witness =>
    let checked := countedFinish input (paddedWitness input.config input.lanes witness) records
    (checked.1, decoded.2 + checked.2)

theorem countedDecodeAndCheck_value (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    (countedDecodeAndCheck input records noWrap).1 = (decodeAndCheck input records noWrap).1 := by
  unfold countedDecodeAndCheck decodeAndCheck
  dsimp only
  cases decoded : (decodeRecords input records noWrap).1 <;> simp [countedFinish_value]

def decodeCheckBound (input : Public) : Nat :=
  input.lanes * ConcreteRowExtraction.rowArithmeticPolynomial (blockLength input.config) + checkerBound input

theorem countedDecodeAndCheck_cost (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config) :
    (countedDecodeAndCheck input records noWrap).2 ≤ decodeCheckBound input := by
  have hd := decodeRecords_decoder_cost input records noWrap redundancy
  unfold countedDecodeAndCheck
  dsimp only
  cases decoded : (decodeRecords input records noWrap).1 with
  | none =>
    dsimp only
    unfold decodeCheckBound
    omega
  | some witness =>
    have hc := countedFinish_cost input (paddedWitness input.config input.lanes witness) records
    dsimp only
    unfold decodeCheckBound
    omega

/-- The source accepted-record parser is reused, with acceptance evaluated exactly once by its counted verifier. -/
def countedAcceptedRecords (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (answers : List Reply) :
    List (Fin (2 ^ depth) × Array E) × Nat :=
  let accepted := countedAcceptedReplies input tape answers
  let records := if accepted.1 then
    let ch := challenges input.config tape
    let proof := decodedOpening input.config ch answers.toArray
    match deriveQueries depth input.config.queries[level.val]! ch.levels[level.val]!.querySqueezes with
    | none => []
    | some positions =>
      if valid : positions.size = input.config.queries[level.val]! ∧
          ∀ i : Fin input.config.queries[level.val]!, positions[i.val]! < 2 ^ depth then
        List.ofFn fun i : Fin input.config.queries[level.val]! =>
          (⟨positions[i.val]!, valid.2 i⟩, proof.levels[level.val]!.rows[i.val]!)
      else []
    else []
  (records, accepted.2)

theorem countedAcceptedRecords_value (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (answers : List Reply) :
    (countedAcceptedRecords input tape level depth answers).1 = acceptedRecords input tape level depth answers := by
  simp only [countedAcceptedRecords, countedAcceptedReplies_value, acceptedRecords]
  rfl

/-- Instrumented legal machine. Counters at a query describe local work already performed, so even fuel exhaustion retains the consumed arithmetic. -/
inductive CountedProgram (c : Config) (lanes : Nat) where
  | finish (output : Option (Witness c lanes)) (fieldArithmetic : Nat)
  | query (fieldArithmetic : Nat) (batches : List Batch) (message : Batch)
      (next : Reply → CountedProgram c lanes)

def CountedProgram.erase {c : Config} {lanes : Nat} : CountedProgram c lanes → RewindProgram c lanes
  | .finish output _ => .finish output
  | .query _ batches message next => .query batches message (fun reply => (next reply).erase)


/-- Consumed 64-bit field words plus structural slots. Every E scalar has three K-sized words. Prover construction time is outside this admission unit. -/
def replyWords : Reply → Nat
  | .initial _ => 7
  | .fold _ next residual =>
      9 + (next.getD #[]).size +
        3 * ((next.getD #[]).toList.map Array.size).sum + 3 * residual.size
  | .ood _ => 10
  | .query rows _ => 7 + rows.size + 3 * (rows.toList.map Array.size).sum
  | .tail _ => 7
structure CountedResult (c : Config) (lanes : Nat) where
  output : Option (Witness c lanes)
  fieldArithmetic : Nat
  responseCalls : Nat
  encodedReplyWords : Nat

def runCounted (input : Public) (strategy : Strategy) (maxReplay : Nat) :
    Nat → CountedProgram input.config input.lanes → CountedResult input.config input.lanes
  | _, .finish output charge => ⟨output, charge, 0, 0⟩
  | 0, .query charge _ _ _ => ⟨none, charge, 0, 0⟩
  | fuel + 1, .query charge batches message next =>
    if batches.length ≤ maxReplay then
      let past := replayPast input strategy [] batches
      let answer := strategy input past message
      let result := runCounted input strategy maxReplay fuel (next answer)
      ⟨result.output, result.fieldArithmetic, result.responseCalls + batches.length + 1,
        result.encodedReplyWords + (past.map (fun entry => replyWords entry.2)).sum + replyWords answer⟩
    else ⟨none, charge, 0, 0⟩

theorem runCounted_value (input : Public) (strategy : Strategy) (maxReplay fuel : Nat)
    (program : CountedProgram input.config input.lanes) :
    (runCounted input strategy maxReplay fuel program).output =
      (runRewind input strategy maxReplay fuel program.erase).output ∧
    (runCounted input strategy maxReplay fuel program).responseCalls =
      (runRewind input strategy maxReplay fuel program.erase).responseCalls := by
  induction fuel generalizing program with
  | zero => cases program <;> simp [runCounted, CountedProgram.erase, runRewind]
  | succ fuel ih =>
    cases program with
    | finish output charge => simp [runCounted, CountedProgram.erase, runRewind]
    | query charge batches message next =>
      simp only [runCounted, CountedProgram.erase, runRewind]
      split
      · exact ⟨(ih _).1, congrArg (· + batches.length + 1) (ih _).2⟩
      · exact ⟨rfl, rfl⟩

def countedTrial (input : Public) (charge : Nat) (historyPrefix : List Batch) :
    List Batch → (List Reply → CountedProgram input.config input.lanes) →
      CountedProgram input.config input.lanes
  | [], finish => finish []
  | message :: rest, finish =>
    .query charge historyPrefix message (fun reply =>
      countedTrial input charge (historyPrefix ++ [message]) rest (fun replies => finish (reply :: replies)))

theorem countedTrial_erase (input : Public) (charge : Nat) (historyPrefix messages : List Batch)
    (finish : List Reply → CountedProgram input.config input.lanes)
    (original : List Reply → RewindProgram input.config input.lanes)
    (equal : ∀ replies, (finish replies).erase = original replies) :
    (countedTrial input charge historyPrefix messages finish).erase =
      trialProgram input historyPrefix messages original := by
  induction messages generalizing historyPrefix finish original with
  | nil => exact equal []
  | cons message messages ih =>
    simp only [countedTrial, CountedProgram.erase, trialProgram]
    congr 1
    funext reply
    exact ih _ _ _ (fun replies => equal (reply :: replies))

def countedCollect (input : Public) (level : Fin input.config.folds.size) (depth : Nat) :
    List (Tape input.config) → Nat →
      (List (Fin (2 ^ depth) × Array E) → Nat → CountedProgram input.config input.lanes) →
        CountedProgram input.config input.lanes
  | [], charge, finish => finish [] charge
  | tape :: tapes, charge, finish =>
    countedTrial input charge [] (visibleBatches input.config tape.1 (challenges input.config tape))
      (fun replies =>
        let accepted := countedAcceptedRecords input tape level depth replies
        countedCollect input level depth tapes (charge + accepted.2)
          (fun records total => finish (accepted.1 ++ records) total))

theorem countedCollect_erase (input : Public) (level : Fin input.config.folds.size) (depth : Nat)
    (tapes : List (Tape input.config)) (charge : Nat)
    (finish : List (Fin (2 ^ depth) × Array E) → Nat → CountedProgram input.config input.lanes)
    (original : List (Fin (2 ^ depth) × Array E) → RewindProgram input.config input.lanes)
    (equal : ∀ records total, (finish records total).erase = original records) :
    (countedCollect input level depth tapes charge finish).erase = continueCollect input level depth tapes original := by
  induction tapes generalizing charge finish original with
  | nil => exact equal [] charge
  | cons tape tapes ih =>
    simp only [countedCollect, continueCollect]
    apply countedTrial_erase
    intro replies
    try dsimp only
    rw [ih _ _ _ (by intro records total; rw [equal])]
    simp only [countedAcceptedRecords_value]

def countedRepeatedProgram (profile : ParameterBounds.Profile) (rounds : Nat) (input : Public)
    (equal : input.config = ParameterBounds.config profile) :
    List (Seed profile rounds) → Nat → CountedProgram input.config input.lanes
  | [], charge => .finish none charge
  | seed :: seeds, charge =>
    countedCollect input (equal.symm ▸ initialLevel profile)
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
      (seedTapes profile rounds input equal seed) charge (fun records total =>
        let decoded := countedDecodeAndCheck input (baseRecords records) (by
          simpa only [equal] using (InitialCandidates.production_initial_facts profile).2.2.1)
        match decoded.1 with
        | some witness => .finish (some witness) (total + decoded.2)
        | none => countedRepeatedProgram profile rounds input equal seeds (total + decoded.2))

theorem countedRepeatedProgram_erase (profile : ParameterBounds.Profile) (rounds : Nat) (input : Public)
    (equal : input.config = ParameterBounds.config profile) (seeds : List (Seed profile rounds)) (charge : Nat) :
    (countedRepeatedProgram profile rounds input equal seeds charge).erase = repeatedProgram profile rounds input equal seeds := by
  induction seeds generalizing charge with
  | nil => rfl
  | cons seed seeds ih =>
    simp only [countedRepeatedProgram, repeatedProgram]
    apply countedCollect_erase
    intro records total
    try dsimp only
    rw [countedDecodeAndCheck_value]
    split <;> simp_all [CountedProgram.erase]

/-- Exact agreement with the existing actual repeated extractor, including all strict-prefix replay responses, not merely independent decoder calls. -/
theorem actualRepeated_value (profile : ParameterBounds.Profile) (rounds attempts lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength (ParameterBounds.config profile))
      (attempts * (rounds * streamLength (ParameterBounds.config profile)))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    let actual := runRewind input strategy (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program input seed)
    measured.output = actual.output ∧ measured.responseCalls = actual.responseCalls := by
  dsimp only
  have h := runCounted_value (ExecutionShapes.Input profile lanes root claims) strategy
    (streamLength (ParameterBounds.config profile))
    (attempts * (rounds * streamLength (ParameterBounds.config profile)))
    (countedRepeatedProgram profile rounds (ExecutionShapes.Input profile lanes root claims)
      rfl (List.ofFn seed) 0)
  simpa [countedRepeatedProgram_erase, repeatedExtractor] using h

end Whir.ExtractorArithmeticCost
