import Whir.ExtractorArithmeticCost

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck

/-- Every reachable program node has a bounded accumulated arithmetic count. The actual factory below proves this property from source counters. -/
def CountedProgram.Bounded {c : Config} {lanes : Nat} (bound : Nat) : CountedProgram c lanes → Prop
  | .finish _ charge => charge ≤ bound
  | .query charge _ _ next => charge ≤ bound ∧ ∀ reply, (next reply).Bounded bound

theorem runCounted_cost (input : Public) (strategy : Strategy) (maxReplay fuel bound : Nat)
    (program : CountedProgram input.config input.lanes) (valid : program.Bounded bound) :
    (runCounted input strategy maxReplay fuel program).fieldArithmetic ≤ bound := by
  induction fuel generalizing program with
  | zero => cases program <;> exact (by first | exact valid | exact valid.1)
  | succ fuel ih =>
    cases program with
    | finish output charge => exact valid
    | query charge batches message next =>
      simp only [runCounted]
      split
      · exact ih _ (valid.2 _)
      · exact valid.1

private theorem countedTrial_bounded (input : Public) (charge bound : Nat)
    (historyPrefix messages : List Batch) (finish : List Reply → CountedProgram input.config input.lanes)
    (charged : charge ≤ bound) (valid : ∀ replies, (finish replies).Bounded bound) :
    (countedTrial input charge historyPrefix messages finish).Bounded bound := by
  induction messages generalizing historyPrefix finish with
  | nil => exact valid []
  | cons message messages ih =>
    exact ⟨charged, fun reply => ih _ _ (fun replies => valid (reply :: replies))⟩

theorem countedCollect_bounded (input : Public) (level : Fin input.config.folds.size)
    (depth : Nat) (tapes : List (Tape input.config)) (charge trialBound bound : Nat)
    (trials : ∀ tape ∈ tapes, ∀ answers,
      (countedAcceptedReplies input tape answers).2 ≤ trialBound)
    (finish : List (Fin (2 ^ depth) × Array E) → Nat → CountedProgram input.config input.lanes)
    (charged : charge + tapes.length * trialBound ≤ bound)
    (valid : ∀ records total, total ≤ charge + tapes.length * trialBound →
      (finish records total).Bounded bound) :
    (countedCollect input level depth tapes charge finish).Bounded bound := by
  induction tapes generalizing charge finish with
  | nil => exact valid [] charge (by simp)
  | cons tape tapes ih =>
    simp only [countedCollect]
    apply countedTrial_bounded input charge bound _ _ _ (by omega)
    intro replies
    try dsimp only
    have cost : (countedAcceptedRecords input tape level depth replies).2 ≤ trialBound :=
      trials tape (by simp) replies
    apply ih (charge + (countedAcceptedRecords input tape level depth replies).2)
      (fun t ht answers => trials t (by simp [ht]) answers) _
    · simp only [List.length_cons, Nat.succ_mul] at charged
      omega
    · intro records total totalBound
      apply valid
      simp only [List.length_cons, Nat.succ_mul]
      omega

theorem seedTapes_length (profile : ParameterBounds.Profile) (rounds : Nat) (input : Public)
    (equal : input.config = ParameterBounds.config profile) (seed : Seed profile rounds) :
    (seedTapes profile rounds input equal seed).length = rounds := by
  cases input with
  | mk config lanes root claims =>
    dsimp only at equal
    subst config
    simp [seedTapes]

/-- A fixed natural trial budget is not an assumed cost model: it is exactly the proved trialPolynomial applied to strict public challenge dimensions. -/
theorem countedRepeatedProgram_bounded (profile : ParameterBounds.Profile) (rounds : Nat)
    (input : Public) (equal : input.config = ParameterBounds.config profile)
    (dimension folds oods queries tail : Nat)
    (consumer : ∀ tape : Tape input.config,
      ChallengeInput input.config (challenges input.config tape) dimension folds oods queries tail)
    (redundancy : width input.config < blockLength input.config)
    (seeds : List (Seed profile rounds)) (charge bound : Nat)
    (charged : charge + seeds.length *
      (rounds * trialPolynomial input.claims.size input.config.folds.size dimension folds oods queries tail +
        decodeCheckBound input) ≤ bound) :
    (countedRepeatedProgram profile rounds input equal seeds charge).Bounded bound := by
  induction seeds generalizing charge with
  | nil => simpa [countedRepeatedProgram, CountedProgram.Bounded] using charged
  | cons seed seeds ih =>
    simp only [countedRepeatedProgram]
    apply countedCollect_bounded input _ _ _ charge
      (trialPolynomial input.claims.size input.config.folds.size dimension folds oods queries tail) bound
    · intro tape _ answers
      exact countedAcceptedReplies_bound input tape answers _ _ _ _ _ (consumer tape)
    · simp only [seedTapes_length]
      simp only [List.length_cons, Nat.succ_mul] at charged
      omega
    · intro records total totalBound
      have cost := countedDecodeAndCheck_cost input (baseRecords records) (by
        simpa only [equal] using (InitialCandidates.production_initial_facts profile).2.2.1) redundancy
      simp only [seedTapes_length] at totalBound
      try dsimp only
      split
      · dsimp [CountedProgram.Bounded]
        simp only [List.length_cons, Nat.succ_mul] at charged
        omega
      · apply ih
        simp only [List.length_cons, Nat.succ_mul] at charged
        omega

def totalFieldPolynomial (input : Public) (attempts rounds dimension folds oods queries tail : Nat) : Nat :=
  attempts * (rounds * trialPolynomial input.claims.size input.config.folds.size
    dimension folds oods queries tail + decodeCheckBound input)

/-- End-to-end arithmetic and interaction bounds on the actual bounded legal repeated extractor, with exact output and response-count correspondence. -/
theorem actualRepeated_cost (profile : ParameterBounds.Profile) (rounds attempts lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) (dimension folds oods queries tail : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        dimension folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile)) :
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength (ParameterBounds.config profile))
      (attempts * (rounds * streamLength (ParameterBounds.config profile)))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    measured.fieldArithmetic ≤ totalFieldPolynomial input attempts rounds dimension folds oods queries tail ∧
      measured.responseCalls ≤ attempts * (rounds * streamLength (ParameterBounds.config profile)) *
        (streamLength (ParameterBounds.config profile) + 1) := by
  dsimp only
  constructor
  · apply runCounted_cost
    apply countedRepeatedProgram_bounded profile rounds _ rfl dimension folds oods queries tail consumer redundancy
    simp [totalFieldPolynomial]
  · rw [(actualRepeated_value profile rounds attempts lanes root claims strategy seed).2]
    exact repeatedExtractor_responseCalls profile attempts rounds ⟨_, strategy⟩ seed

end Whir.ExtractorArithmeticCost
