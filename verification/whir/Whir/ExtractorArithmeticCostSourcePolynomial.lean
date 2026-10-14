import Whir.ExtractorArithmeticCostSourceResources

/-! Polynomial source-extractor arithmetic in actual physical cube length S, row nodes N, padded lanes, original families and points, attempts and reset trials. The Gao term is degree seven in N. Logarithmic dimension is not relabelled as physical length, and the source map's 75 operations remain literal. -/
namespace Whir.ExtractorArithmeticCostSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck ExtractorArithmeticCost

set_option maxHeartbeats 4000000
attribute [local irreducible] ParameterBounds.config

def physicalSourceFieldPolynomial (paddedLanes occupied cube nodes families points levels attempts rounds folds oods queries tail : Nat) : Nat :=
  OriginalClaimsChecker.preparationFieldPolynomial cube families points +
    attempts * (families + 77 * families * cube + 64 * (2 * families + 77) +
      rounds * physicalTrialPolynomial paddedLanes nodes (points + 2) levels folds oods queries tail +
      occupied * ConcreteRowExtraction.rowArithmeticPolynomial nodes + checkerPolynomial paddedLanes nodes 0 +
      OriginalClaimsChecker.checkFieldPolynomial cube families points)

theorem totalFieldPolynomial_physical (c : Config) (lanes families points attempts rounds folds oods queries tail : Nat)
    (foldBound : c.folds[0]! ≤ c.logN)
    (noWrap : c.logN - c.folds[0]! + c.rates[0]! ≤ 64) :
    totalFieldPolynomial c lanes families points attempts rounds c.logN folds oods queries tail ≤
      physicalSourceFieldPolynomial (laneCount c) lanes (2 ^ c.logN) (blockLength c) families points c.folds.size
        attempts rounds folds oods queries tail := by
  have width := denseWidth_le_physical c foldBound
  have trial : trialPolynomial (points + 2) c.folds.size c.logN folds oods queries tail ≤
      physicalTrialPolynomial (laneCount c) (blockLength c) (points + 2) c.folds.size folds oods queries tail := by
    unfold trialPolynomial verifierPolynomial levelPolynomial physicalTrialPolynomial physicalLevelPolynomial
    simp only [Nat.add_assoc, Nat.mul_assoc] at *
    gcongr
  have common : encoderBound c ≤ checkerPolynomial (laneCount c) (blockLength c) 0 := by
    simpa only [checkerBound, Array.size_empty, Nat.zero_mul, Nat.add_zero] using
      checkerBound_polynomial (⟨c, lanes, #[], #[]⟩ : Public) noWrap
  have transformation : OriginalClaimsChecker.transformationField c families =
      families + 77 * families * 2 ^ c.logN + 64 * (2 * families + 77) := by
    simp only [OriginalClaimsChecker.transformationField, OriginalClaimsChecker.mapField_eq]
    ring
  unfold totalFieldPolynomial oneFieldPolynomial physicalSourceFieldPolynomial
  rw [transformation]
  gcongr

theorem run_physical_field {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds)
    (folds oods queries tail : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        (ParameterBounds.config profile).logN folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile)) :
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).fieldArithmetic ≤
      physicalSourceFieldPolynomial (laneCount (ParameterBounds.config profile)) lanes
        (2 ^ (ParameterBounds.config profile).logN) (blockLength (ParameterBounds.config profile)) m points.size
        (ParameterBounds.config profile).folds.size attempts rounds folds oods queries tail := by
  have arithmetic := run_cost profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed
    (ParameterBounds.config profile).logN folds oods queries tail consumer redundancy
  exact arithmetic.1.trans (totalFieldPolynomial_physical (ParameterBounds.config profile) lanes m points.size
    attempts rounds folds oods queries tail (InitialCandidates.production_initial_facts profile).2.1
    (InitialCandidates.production_initial_facts profile).2.2.1)

#print axioms run_physical_field

end Whir.ExtractorArithmeticCostSource
