import Whir.PCSRewindKnowledgeProduction

/-! A pointwise mass bound lets fresh public compression be averaged without
assuming that every public prefix has the overall acceptance advantage. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability AuthenticatedResetSupport
open ResetAcceptanceAmplification

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] ParameterBounds.config

 theorem production_single_attempt_mass (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) (gap : ℝ) (gapPositive : 0 < gap)
    (large : (knowledgeBadEnvelope : ℝ) + 2 * (heavyQueryLoss profile : ℝ) + gap <
      probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)) :
    (probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true) -
      (knowledgeBadEnvelope : ℝ)) / 4 ≤
      probability (extractionSuccess (extractor profile (knowledgeRounds profile gap))
        ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩) := by
  classical
  have acceptanceLeOne := le_one
    (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)
  have lossNonnegative : (0 : ℝ) ≤ (heavyQueryLoss profile : ℝ) := by
    unfold heavyQueryLoss
    positivity
  have badNonnegative : (0 : ℝ) ≤ (knowledgeBadEnvelope : ℝ) := by
    norm_num [knowledgeBadEnvelope]
  have gapLeOne : gap ≤ 1 := by linarith
  let safe := fun draw : Tape (ParameterBounds.config profile) × TrialSeed profile =>
    safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) draw.1 draw.2
  have mass := production_safe_mass profile lanes root claims strategy laneBound claimShape claimCap
  have conditional : ∀ base, GoodPrefix safe base →
      1 - (1 / 4 : ℝ) ≤ probability (fun seed : Fin (knowledgeRounds profile gap) → TrialSeed profile =>
        extractionSuccess (extractor profile (knowledgeRounds profile gap))
          ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (base, seed)) := by
    intro base good
    have conditionalMass := good
    change probability safe / 2 ≤ probability _ at conditionalMass
    have scale : (blockLength (ParameterBounds.config profile) : ℝ) * heavyAvailability profile gap = gap / 4 := by
      unfold heavyAvailability
      push_cast
      field_simp [show (blockLength (ParameterBounds.config profile) : ℝ) ≠ 0 by positivity]
    have heavyMass : (heavyQueryLoss profile : ℝ) +
        blockLength (ParameterBounds.config profile) * heavyAvailability profile gap <
        probability (safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base) := by
      rw [scale]
      dsimp only [safe] at conditionalMass
      linarith
    let certificate := Classical.choice (production_heavy_witness profile lanes root claims strategy base
      (heavyAvailability profile gap) (heavyAvailability_positive profile gap gapPositive) heavyMass)
    have recovered := conditional_extractor_schedule profile lanes root claims strategy laneBound
      (productionBad profile lanes root claims strategy) base (heavyAvailability profile gap)
      (heavyAvailability_positive profile gap gapPositive) (heavyAvailability_le_one profile gap gapLeOne)
      (availabilityBlock profile gap) 0 (availabilityBlock_enough profile gap gapPositive) heavyMass certificate
    change 1 - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ 0 ≤ _ at recovered
    convert recovered using 1 <;> simp only [knowledgeRounds, pow_zero, mul_one]
    unfold probability
    congr 1
  have chance := prefix_attempt_chance safe
    (extractionSuccess (extractor profile (knowledgeRounds profile gap))
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩)
    (1 / 4 : ℝ) (by norm_num) (by norm_num) conditional
  dsimp only [safe] at chance
  nlinarith

#print axioms production_single_attempt_mass
#check production_single_attempt_mass
end Whir.PCSRewindExtractor
