import Whir.PCSRewindKnowledgeOriginalRepeated
import Whir.PCSRewindSourceRelation
import Whir.ExtractorArithmeticCostSourceComparisons

/-! Complete interactive reset-extraction endpoints for the original statement.
The acceptance probability chooses proof fuel, not an executable probability
estimator. Runtime charges the actual source machine and literal admitted reply
words, with external prover computation outside the unit-oracle boundary. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open PCSRewindExtractor SamplingProbability OriginalClaimsChecker
open scoped BigOperators

set_option maxHeartbeats 4000000
attribute [local irreducible] ParameterBounds.config

theorem complete_original_knowledge {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy)
    (familyCap : m ≤ 2 ^ 64) (claimCap : points.size + 2 ≤ 2 ^ 64) (security : Nat) :
    let κ := probability (accepted profile lanes family points anchorPoint anchorValue root strategy)
    let gap := κ - (extractionCutoff : ℝ)
    let attempts := sourceAttempts gap security
    let rounds := sourceRounds profile gap
    (∀ seed : RepeatedSeed profile attempts rounds,
      ∀ w : Witness (ParameterBounds.config profile) lanes,
        (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).output = some w →
        ExplainsOriginal (ParameterBounds.config profile) lanes root family points anchorPoint anchorValue w) ∧
    probability (failureEvent profile attempts rounds lanes family points anchorPoint anchorValue root strategy) ≤
      (extractionCutoff : ℝ) + (1 / 2 : ℝ) ^ security ∧
    (0 < gap →
      (rounds : ℝ) ≤ ((8 * blockLength (ParameterBounds.config profile) : ℝ) / gap + 1) *
        ((initialDepth profile : ℝ) + 2) ∧
      (attempts : ℝ) ≤ ((8 : ℝ) / gap + 1) * security) := by
  dsimp only
  refine ⟨?_, universal_knowledge_failure profile lanes family points anchorPoint anchorValue root strategy
    familyCap claimCap security, ?_⟩
  · intro seed w output
    exact run_output_explains profile _ _ lanes family points anchorPoint anchorValue root strategy seed w output
  · intro positive
    exact ⟨sourceRounds_polynomial profile _ positive, sourceAttempts_polynomial _ positive security⟩

/-- Profile tables discharge challenge-shape and redundancy requirements even for
malformed or withholding strategies. The root rectangle, occupied-lane limit,
and literal reply-word admission remain explicit physical input restrictions. -/
theorem complete_original_resource {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seed : RepeatedSeed profile attempts rounds) (encodedWords : Nat)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (admitted : (ExtractorArithmeticCostSource.run profile attempts rounds lanes family points anchorPoint anchorValue
      root strategy seed).encodedReplyWords ≤ encodedWords) :
    let c := ParameterBounds.config profile
    let measured := ExtractorArithmeticCostSource.run profile attempts rounds lanes family points anchorPoint anchorValue
      root strategy seed
    measured.fieldArithmetic + measured.responseCalls + measured.encodedReplyWords +
      ExtractorArithmeticCostSource.originalReservation c lanes attempts family points anchorPoint anchorValue +
      (∑ i, ExtractorArithmeticCostSource.retainedCharge profile rounds lanes family points anchorPoint anchorValue
        prepared root strategy (seed i)) +
      (∑ i, ExtractorArithmeticCostSource.commonComparisonReservation c
        (ExtractorArithmeticCostSource.sourceRecords profile rounds lanes family points anchorPoint anchorValue
          prepared root strategy (seed i)).length) ≤
    ExtractorArithmeticCostSource.physicalSourceFieldPolynomial (laneCount c) lanes (2 ^ c.logN)
      (blockLength c) m points.size c.folds.size attempts rounds 6 256 256 c.logN +
      attempts * ((rounds * streamLength c) * (streamLength c + 1)) + encodedWords +
      ExtractorArithmeticCostSource.originalReservationPolynomial c m points.size attempts +
      attempts * ExtractorArithmeticCost.retainedPreparationPolynomial c rounds lanes (points.size + 2) +
      attempts * ExtractorArithmeticCostSource.commonComparisonPolynomial c rounds := by
  exact ExtractorArithmeticCostSource.run_complete_physical_resource profile attempts rounds lanes family points
    anchorPoint anchorValue prepared root strategy seed 6 256 256 (ParameterBounds.config profile).logN encodedWords
    (production_challenge_input profile) (production_heavy_static profile).2.1 physicalRoot physicalLanes
    prepared.guards.2.2.2.1 admitted

#print axioms complete_original_knowledge
#print axioms complete_original_resource
#check complete_original_knowledge
#check complete_original_resource
end Whir.PCSRewindSource
