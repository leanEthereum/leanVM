import Whir.ExtractorArithmeticCostSourcePolynomial

/-! The actual source common-coordinate matcher and coordinate deduplication comparisons have their own counter, separate from field arithmetic. Full source extractor resource composition includes these comparisons, literal retained-row preparation, immutable original preparation/check reservations and strict-prefix oracle access. -/
namespace Whir.ExtractorArithmeticCostSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck ExtractorArithmeticCost
open scoped BigOperators

set_option maxHeartbeats 4000000
attribute [local irreducible] ParameterBounds.config

def commonComparisonPolynomial (c : Config) (rounds : Nat) : Nat :=
  (rounds * c.queries[0]!) * (1 + 3 * laneCount c) +
    (rounds * c.queries[0]!) * (rounds * c.queries[0]! + 1)

def sourceRecords {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds) :=
  retainedRecords profile rounds lanes root (OriginalClaimsChecker.input prepared root seed.1).claims
    (strategy seed.1) seed.2

theorem sourceRecords_count {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds) :
    (sourceRecords profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).length ≤
      rounds * (ParameterBounds.config profile).queries[0]! := by
  exact (List.length_filterMap_le _ _).trans
    (production_collected_records profile rounds lanes root
      (OriginalClaimsChecker.input prepared root seed.1).claims (strategy seed.1) seed.2)

theorem source_common_value_and_cost {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds)
    (candidate : Array E) :
    let records := sourceRecords profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
    (countedCommonCoordinates (ParameterBounds.config profile) lanes candidate records).1 =
      commonCoordinates (ParameterBounds.config profile) lanes candidate records ∧
    (countedCommonCoordinates (ParameterBounds.config profile) lanes candidate records).2 ≤
      commonComparisonPolynomial (ParameterBounds.config profile) rounds := by
  dsimp only
  constructor
  · exact countedCommonCoordinates_value _ _ _ _
  · have comparisons := countedCommonCoordinates_cost (ParameterBounds.config profile) lanes candidate
      (sourceRecords profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed)
    have records := sourceRecords_count profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
    unfold commonComparisonPolynomial
    exact comparisons.trans (by gcongr)

def commonComparisonReservation (c : Config) (records : Nat) : Nat :=
  records * (1 + 3 * laneCount c) + records * (records + 1)

theorem all_common_comparison_reservations {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds) :
    (∑ i, commonComparisonReservation (ParameterBounds.config profile)
      (sourceRecords profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed i)).length) ≤
      attempts * commonComparisonPolynomial (ParameterBounds.config profile) rounds := by
  calc
    _ ≤ ∑ _i : Fin attempts, commonComparisonPolynomial (ParameterBounds.config profile) rounds := by
      apply Finset.sum_le_sum
      intro i _
      have records := sourceRecords_count profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed i)
      unfold commonComparisonReservation commonComparisonPolynomial
      gcongr
    _ = _ := by simp

/-- Complete actual legal source run resource polynomial. Every original and retained input restriction is explicit, no honest-root recomputation is assumed, and consumed response words are charged by literal U. The external prover is a unit oracle-access boundary, not a purported machine-time-efficient algorithm. -/
theorem run_complete_physical_resource {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seed : PCSRewindSource.RepeatedSeed profile attempts rounds)
    (folds oods queries tail encodedWords : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        (ParameterBounds.config profile).logN folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile))
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (admitted : (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).encodedReplyWords ≤ encodedWords) :
    let c := ParameterBounds.config profile
    let measured := run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed
    measured.fieldArithmetic + measured.responseCalls + measured.encodedReplyWords +
      originalReservation c lanes attempts family points anchorPoint anchorValue +
      (∑ i, retainedCharge profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed i)) +
      (∑ i, commonComparisonReservation c
        (sourceRecords profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed i)).length) ≤
    physicalSourceFieldPolynomial (laneCount c) lanes (2 ^ c.logN) (blockLength c) m points.size c.folds.size
      attempts rounds folds oods queries tail +
      attempts * ((rounds * streamLength c) * (streamLength c + 1)) + encodedWords +
      originalReservationPolynomial c m points.size attempts +
      attempts * retainedPreparationPolynomial c rounds lanes (points.size + 2) +
      attempts * commonComparisonPolynomial c rounds := by
  dsimp only
  have complete := run_complete_resource profile attempts rounds lanes family points anchorPoint anchorValue prepared root strategy seed
    (ParameterBounds.config profile).logN folds oods queries tail encodedWords consumer redundancy
    physicalRoot physicalLanes occupied admitted
  have physical := totalFieldPolynomial_physical (ParameterBounds.config profile) lanes m points.size attempts rounds folds oods queries tail
    (InitialCandidates.production_initial_facts profile).2.1 (InitialCandidates.production_initial_facts profile).2.2.1
  have comparisons := all_common_comparison_reservations profile attempts rounds lanes family points anchorPoint anchorValue prepared
    root strategy seed
  omega

#print axioms source_common_value_and_cost
#print axioms run_complete_physical_resource

end Whir.ExtractorArithmeticCostSource
