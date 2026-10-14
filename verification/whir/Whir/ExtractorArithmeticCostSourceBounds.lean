import Whir.ExtractorArithmeticCostSource
import Whir.ExtractorArithmeticCostPolynomial

/-! Complete arithmetic and strict-prefix interaction budgets for the executable original-source wrapper. Public dimensions bound resource consumption independently of verifier acceptance. Decoder arithmetic is the concrete degree-seven Root0 Gao bound; no intermediate GS backend occurs. -/
namespace Whir.ExtractorArithmeticCostSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck ExtractorArithmeticCost

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
attribute [local irreducible] ParameterBounds.config

theorem program_bounded (input : Public) (level : Fin input.config.folds.size) (tapes : List (Tape input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config) (families points : Nat)
    (checker : Witness input.config input.lanes → Bool × OriginalClaimsChecker.Work)
    (originalBound : ∀ w, (checker w).2.fieldArithmetic ≤
      OriginalClaimsChecker.checkFieldPolynomial (2 ^ input.config.logN) families points)
    (dimension folds oods queries tail : Nat)
    (consumer : ∀ tape ∈ tapes,
      ChallengeInput input.config (challenges input.config tape) dimension folds oods queries tail) :
    (program input level tapes noWrap checker).Bounded
      (tapes.length * trialPolynomial input.claims.size input.config.folds.size dimension folds oods queries tail +
        decodedBound input families points) := by
  unfold program
  apply countedCollect_bounded input level _ tapes 0
    (trialPolynomial input.claims.size input.config.folds.size dimension folds oods queries tail)
  · intro tape member answers
    exact countedAcceptedReplies_bound input tape answers _ _ _ _ _ (consumer tape member)
  · omega
  · intro records total totalBound
    have decodeCost := decoded_field input (baseRecords records) noWrap redundancy families points checker originalBound
    dsimp only [CountedProgram.Bounded]
    omega

theorem input_claim_count {c : Config} {lanes m : Nat} {family : Fin m → RingPCSGame.FamilyClaim}
    {points : Array RingPCSGame.PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : OriginalClaimsChecker.Prepared c lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (publicPrefix : RingPCSGame.Prefix) :
    (OriginalClaimsChecker.input prepared root publicPrefix).claims.size = points.size + 2 := by
  simp [OriginalClaimsChecker.input, prepared.pointClaims_eq]
  omega

def oneFieldPolynomial (c : Config) (lanes families points rounds dimension folds oods queries tail : Nat) : Nat :=
  OriginalClaimsChecker.transformationField c families +
    rounds * trialPolynomial (points + 2) c.folds.size dimension folds oods queries tail +
    lanes * ConcreteRowExtraction.rowArithmeticPolynomial (blockLength c) + encoderBound c +
    OriginalClaimsChecker.checkFieldPolynomial (2 ^ c.logN) families points

theorem runOne_field {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds)
    (dimension folds oods queries tail : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        dimension folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile)) :
    (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).fieldArithmetic ≤
      oneFieldPolynomial (ParameterBounds.config profile) lanes m points.size rounds dimension folds oods queries tail := by
  let inp := OriginalClaimsChecker.input prepared root seed.1
  have bound := program_bounded inp (initialLevel profile) (seedTapes profile rounds inp rfl seed.2)
    (InitialCandidates.production_initial_facts profile).2.2.1 redundancy m points.size
    (OriginalClaimsChecker.countedCheck prepared) (OriginalClaimsChecker.countedCheck_field prepared)
    dimension folds oods queries tail (fun tape _ => consumer tape)
  have actual := runCounted_cost inp (strategy seed.1) (streamLength inp.config)
    (rounds * streamLength inp.config) _ _ bound
  have claims : inp.claims.size = points.size + 2 := input_claim_count prepared root seed.1
  rw [seedTapes_length profile rounds inp rfl seed.2, claims] at actual
  have decodeBudget : decodedBound inp m points.size =
      lanes * ConcreteRowExtraction.rowArithmeticPolynomial (blockLength (ParameterBounds.config profile)) +
        encoderBound (ParameterBounds.config profile) +
        OriginalClaimsChecker.checkFieldPolynomial (2 ^ (ParameterBounds.config profile).logN) m points.size := by
    unfold decodedBound checkerBound
    change lanes * ConcreteRowExtraction.rowArithmeticPolynomial (blockLength (ParameterBounds.config profile)) +
      (encoderBound (ParameterBounds.config profile) + 0 * _) + _ = _
    simp only [Nat.zero_mul, Nat.add_zero]
    rfl
  have trialBudget : trialPolynomial (points.size + 2) inp.config.folds.size dimension folds oods queries tail =
      trialPolynomial (points.size + 2) (ParameterBounds.config profile).folds.size dimension folds oods queries tail := rfl
  rw [decodeBudget, trialBudget] at actual
  unfold runOne
  dsimp only [OriginalClaimsChecker.countedInput]
  unfold oneFieldPolynomial
  dsimp only [inp, OriginalClaimsChecker.transformationWork] at actual ⊢
  omega

theorem runOne_calls {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds) :
    (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).responseCalls ≤
      (rounds * streamLength (ParameterBounds.config profile)) * (streamLength (ParameterBounds.config profile) + 1) := by
  rw [(runOne_value profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).2]
  exact responseCalls_le _ _ _ _ _

theorem runAttempts_field {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seeds : List (PCSRewindSource.Seed profile rounds))
    (dimension folds oods queries tail : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        dimension folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile)) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).fieldArithmetic ≤
      seeds.length * oneFieldPolynomial (ParameterBounds.config profile) lanes m points.size rounds dimension folds oods queries tail := by
  induction seeds with
  | nil => simp [runAttempts]
  | cons seed seeds ih =>
    have first := runOne_field profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
      dimension folds oods queries tail consumer redundancy
    simp only [runAttempts]
    split <;> dsimp only <;> simp only [List.length_cons, Nat.succ_mul] <;> omega

theorem runAttempts_calls {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seeds : List (PCSRewindSource.Seed profile rounds)) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).responseCalls ≤
      seeds.length * ((rounds * streamLength (ParameterBounds.config profile)) * (streamLength (ParameterBounds.config profile) + 1)) := by
  induction seeds with
  | nil => simp [runAttempts]
  | cons seed seeds ih =>
    have first := runOne_calls profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
    simp only [runAttempts]
    split <;> dsimp only <;> simp only [List.length_cons, Nat.succ_mul] <;> omega

def totalFieldPolynomial (c : Config) (lanes families points attempts rounds dimension folds oods queries tail : Nat) : Nat :=
  OriginalClaimsChecker.preparationFieldPolynomial (2 ^ c.logN) families points +
    attempts * oneFieldPolynomial c lanes families points rounds dimension folds oods queries tail

theorem run_cost {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds)
    (dimension folds oods queries tail : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        dimension folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile)) :
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).fieldArithmetic ≤
      totalFieldPolynomial (ParameterBounds.config profile) lanes m points.size attempts rounds dimension folds oods queries tail ∧
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).responseCalls ≤
      attempts * ((rounds * streamLength (ParameterBounds.config profile)) * (streamLength (ParameterBounds.config profile) + 1)) := by
  have preparation := OriginalClaimsChecker.countedPrepare_field (ParameterBounds.config profile) lanes family points anchorPoint anchorValue
  unfold run
  dsimp only
  split
  · dsimp only
    unfold totalFieldPolynomial
    exact ⟨by omega, Nat.zero_le _⟩
  · rename_i prepared _
    have field := runAttempts_field profile rounds lanes family points anchorPoint anchorValue prepared root strategy
      (List.ofFn seed) dimension folds oods queries tail consumer redundancy
    have calls := runAttempts_calls profile rounds lanes family points anchorPoint anchorValue prepared root strategy (List.ofFn seed)
    simp only [List.length_ofFn] at field calls
    dsimp only
    unfold totalFieldPolynomial
    exact ⟨by omega, calls⟩

#print axioms run_cost

end Whir.ExtractorArithmeticCostSource
