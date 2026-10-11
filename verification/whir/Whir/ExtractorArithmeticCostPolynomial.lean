import Whir.ExtractorArithmeticCostBounds
import Whir.CountedCandidateCheckLoops

/-! The dimensions in the polynomial are physical lanes and nodes, not a logarithmic dimension misleadingly called polynomial. Encoded input words U are an explicit admission charge. External prover runtime and raw allocation are outside the oracle-access boundary, even for rejected responses. -/
namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck

def physicalLevelPolynomial (lanes nodes folds oods queries : Nat) : Nat :=
  folds * (3 * lanes * nodes + 6) + oods * (5 * lanes * nodes + 7) +
    (queries + 1) * (16586 + 12 * lanes * nodes)

def physicalTrialPolynomial (lanes nodes claims levels folds oods queries tail : Nat) : Nat :=
  claims * (2 * lanes * nodes + 3) +
    levels * physicalLevelPolynomial lanes nodes folds oods queries +
    tail * (3 * lanes * nodes + 6) + 5 * lanes * nodes + 1

def physicalFieldPolynomial (lanes occupied nodes claims levels attempts rounds folds oods queries tail : Nat) : Nat :=
  attempts * (rounds * physicalTrialPolynomial lanes nodes claims levels folds oods queries tail +
    occupied * ConcreteRowExtraction.rowArithmeticPolynomial nodes + checkerPolynomial lanes nodes claims)

theorem denseWidth_le_physical (c : Config) (foldBound : c.folds[0]! ≤ c.logN) :
    2 ^ c.logN ≤ laneCount c * blockLength c := by
  have eq : 2 ^ c.logN = laneCount c * width c := by
    dsimp [laneCount, width]
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [eq]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
  omega

theorem totalFieldPolynomial_physical (input : Public) (attempts rounds folds oods queries tail : Nat)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    totalFieldPolynomial input attempts rounds input.config.logN folds oods queries tail ≤
      physicalFieldPolynomial (laneCount input.config) input.lanes (blockLength input.config)
        input.claims.size input.config.folds.size attempts rounds folds oods queries tail := by
  have width := denseWidth_le_physical input.config foldBound
  have checker := checkerBound_polynomial input noWrap
  unfold totalFieldPolynomial trialPolynomial verifierPolynomial levelPolynomial decodeCheckBound
    physicalFieldPolynomial physicalTrialPolynomial physicalLevelPolynomial
  simp only [Nat.add_assoc, Nat.mul_assoc] at *
  gcongr

/-- Complete field-plus-oracle-access resource count. U is charged literally, not hidden in a unit-cost call; no timing assertion about external computation is made. The strict physical root/claims/output restrictions remain explicit. -/
theorem actualRepeated_total_resource (profile : ParameterBounds.Profile) (rounds attempts lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) (folds oods queries tail encodedInputWords : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        (ParameterBounds.config profile).logN folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile))
    (_physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (_physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (_occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (_physicalClaims : ∀ claim ∈ claims.toList,
      claim.weight.size = laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile))
    (admittedInput :
      let input := ExecutionShapes.Input profile lanes root claims
      let measured := runCounted input strategy (streamLength input.config)
        (attempts * (rounds * streamLength input.config))
        (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
      measured.encodedReplyWords + consumedWords input [] ≤ encodedInputWords) :
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength input.config)
      (attempts * (rounds * streamLength input.config))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    measured.fieldArithmetic + measured.responseCalls +
      (measured.encodedReplyWords + consumedWords input []) ≤
      physicalFieldPolynomial (laneCount input.config) lanes (blockLength input.config)
        claims.size input.config.folds.size attempts rounds folds oods queries tail +
      attempts * (rounds * streamLength input.config) * (streamLength input.config + 1) +
      encodedInputWords := by
  dsimp only
  have cost := actualRepeated_cost profile rounds attempts lanes root claims strategy seed
    (ParameterBounds.config profile).logN folds oods queries tail consumer redundancy
  have polynomial := totalFieldPolynomial_physical (ExecutionShapes.Input profile lanes root claims)
    attempts rounds folds oods queries tail (InitialCandidates.production_initial_facts profile).2.1
    (InitialCandidates.production_initial_facts profile).2.2.1
  exact Nat.add_le_add (Nat.add_le_add (cost.1.trans polynomial) cost.2) admittedInput

/-- Separately charged, value-connected finite lookup/received-row work. It is not silently included in the field units and does not depend on acceptance. -/
theorem admitted_preparation_resource (input : Public) (records : List (Record input.config))
    (recordLimit claimLimit : Nat) (consumer : ConsumerInput input recordLimit claimLimit records) :
    (countedReceivedTables input records).2 + consumedWords input records ≤
      blockLength input.config * recordLimit + input.lanes * blockLength input.config +
      publicHeaderWords input.config + blockLength input.config * (input.lanes + 1) +
      claimLimit * (3 * laneCount input.config * width input.config + 4) +
      recordLimit * (input.lanes + 2) := by
  have prep := (countedReceivedTables_cost input records).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ consumer.recordCount) _)
  have words := consumedWords_bound input records recordLimit claimLimit consumer
  omega

#print axioms actualRepeated_total_resource
#print axioms admitted_preparation_resource

end Whir.ExtractorArithmeticCost
