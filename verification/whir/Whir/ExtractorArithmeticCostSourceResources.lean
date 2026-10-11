import Whir.ExtractorArithmeticCostSourceBounds
import Whir.ExtractorArithmeticCostRetained

/-! Explicit original-source data, loop and oracle-access boundary. The public physical root shape is a literal consumer restriction, not a conclusion of acceptance. The retained-row charge covers real filled-record lookups and materialized lane tables. All potential original-check and preparation reservations bound the actually visited stopping prefix. Prover CPU time and unbounded raw response allocation remain external; every consumed encoded word is explicitly admitted by U. -/
namespace Whir.ExtractorArithmeticCostSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck ExtractorArithmeticCost
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
attribute [local irreducible] ParameterBounds.config

theorem input_weight_sizes {c : Config} {lanes m : Nat} {family : Fin m → RingPCSGame.FamilyClaim}
    {points : Array RingPCSGame.PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : OriginalClaimsChecker.Prepared c lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (publicPrefix : RingPCSGame.Prefix) :
    ∀ claim ∈ (OriginalClaimsChecker.input prepared root publicPrefix).claims.toList,
      claim.weight.size = 2 ^ c.logN := by
  intro claim member
  rw [OriginalClaimsChecker.input_claims] at member
  simp only [RingPCSGame.transformedClaims, Array.toList_push, Array.toList_append,
    Array.toList_map, List.mem_append, List.mem_singleton, List.mem_map] at member
  rcases member with (compressed | pointed) | anchored
  · subst claim
    simp [RingPCSGame.familyPublic]
  · obtain ⟨point, _, equal⟩ := pointed
    subst claim
    simp [RingPCSGame.publicPoint]
  · subst claim
    simp [CommitmentAnchor.weight]

theorem cube_size (c : Config) (foldBound : c.folds[0]! ≤ c.logN) :
    2 ^ c.logN = laneCount c * width c := by
  unfold laneCount width
  rw [← Nat.pow_add]
  congr 1
  omega

def retainedCharge {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds) : Nat :=
  retainedPreparation profile rounds lanes root (OriginalClaimsChecker.input prepared root seed.1).claims
    (strategy seed.1) seed.2

theorem retainedCharge_bound {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile)) :
    retainedCharge profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed ≤
      retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes (points.size + 2) := by
  have weights := input_weight_sizes prepared root seed.1
  rw [cube_size (ParameterBounds.config profile) (InitialCandidates.production_initial_facts profile).2.1] at weights
  have cost := production_retained_preparation profile rounds lanes root
    (OriginalClaimsChecker.input prepared root seed.1).claims (strategy seed.1) seed.2
    physicalRoot physicalLanes occupied weights
  rw [input_claim_count] at cost
  exact cost

def originalReservation (c : Config) (lanes attempts : Nat) {m : Nat}
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) : Nat :=
  (OriginalClaimsChecker.countedPrepare c lanes family points anchorPoint anchorValue).2.total +
    attempts * ((OriginalClaimsChecker.transformationWork c m points.size).total +
      (OriginalClaimsChecker.checkWork c lanes m points.size 0).total)

def originalReservationPolynomial (c : Config) (families points attempts : Nat) : Nat :=
  OriginalClaimsChecker.preparationPolynomial (2 ^ c.logN) families points +
    attempts * (OriginalClaimsChecker.transformationPolynomial (2 ^ c.logN) families points +
      OriginalClaimsChecker.checkPolynomial (2 ^ c.logN) families points)

theorem transformationWork_total (c : Config) (families points : Nat) :
    (OriginalClaimsChecker.transformationWork c families points).total =
      OriginalClaimsChecker.transformationPolynomial (2 ^ c.logN) families points := by
  simp only [OriginalClaimsChecker.transformationWork, OriginalClaimsChecker.transformationField,
    OriginalClaimsChecker.Work.total, OriginalClaimsChecker.mapField_eq]
  unfold OriginalClaimsChecker.transformationPolynomial
  ring

theorem originalReservation_bound (c : Config) (lanes attempts : Nat) {m : Nat}
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (foldBound : c.folds[0]! ≤ c.logN) (occupied : lanes ≤ laneCount c) :
    originalReservation c lanes attempts family points anchorPoint anchorValue ≤
      originalReservationPolynomial c m points.size attempts := by
  have words : lanes * 2 ^ (c.logN - c.folds[0]!) ≤ 2 ^ c.logN := by
    rw [cube_size c foldBound]
    exact Nat.mul_le_mul_right _ occupied
  have check := OriginalClaimsChecker.checkWork_total c lanes m points.size 0 words (Nat.zero_le _)
  have prepare := OriginalClaimsChecker.countedPrepare_total c lanes family points anchorPoint anchorValue
  unfold originalReservation originalReservationPolynomial
  rw [transformationWork_total]
  exact Nat.add_le_add prepare (Nat.mul_le_mul_left _ (Nat.add_le_add_left check _))

/-- One executable source run plus all admitted encoded replies and a conservative separate reservation for original data/loops. The reservation deliberately includes its field component as well, so the displayed total is an upper accounting unit, not a claim of equality with machine instructions. -/
theorem run_total_resource {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds)
    (dimension folds oods queries tail encodedWords : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        dimension folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile))
    (_physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (_physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (admitted : (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).encodedReplyWords ≤ encodedWords) :
    let measured := run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed
    measured.fieldArithmetic + measured.responseCalls + measured.encodedReplyWords +
      originalReservation (ParameterBounds.config profile) lanes attempts family points anchorPoint anchorValue ≤
    totalFieldPolynomial (ParameterBounds.config profile) lanes m points.size attempts rounds dimension folds oods queries tail +
      attempts * ((rounds * streamLength (ParameterBounds.config profile)) * (streamLength (ParameterBounds.config profile) + 1)) +
      encodedWords + originalReservationPolynomial (ParameterBounds.config profile) m points.size attempts := by
  dsimp only
  have arithmetic := run_cost profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed
    dimension folds oods queries tail consumer redundancy
  have originals := originalReservation_bound (ParameterBounds.config profile) lanes attempts family points anchorPoint anchorValue
    (InitialCandidates.production_initial_facts profile).2.1 occupied
  omega

/-- Summed actual source-prefix retained preparations, hence also every actually visited stopping subset. Root and original statement arrays remain immutable, whereas each seed's public compression and causal prover strategy are the actual ones. -/
theorem all_retained_source_resources {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile)) :
    (∑ i, retainedCharge profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed i)) ≤
      attempts * retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes (points.size + 2) := by
  calc
    _ ≤ ∑ _i : Fin attempts,
        retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes (points.size + 2) :=
      Finset.sum_le_sum (fun i _ => retainedCharge_bound profile rounds lanes family points anchorPoint anchorValue
        prepared root strategy (seed i) physicalRoot physicalLanes occupied)
    _ = _ := by simp

theorem fixed_output_length {c : Config} {lanes m : Nat} {family : Fin m → RingPCSGame.FamilyClaim}
    {points : Array RingPCSGame.PointClaim} {anchorPoint : Array E} {anchorValue : E}
    (prepared : OriginalClaimsChecker.Prepared c lanes m family points anchorPoint anchorValue)
    (w : Witness c lanes) :
    (Array.ofFn w).size = lanes * width c ∧ (Array.ofFn w).size ≤ 2 ^ c.logN := by
  have occupied := OriginalClaimsChecker.guarded_occupied_le c lanes family points anchorPoint prepared.guards
  constructor
  · simp [width]
  · simpa [width] using occupied

theorem run_complete_resource {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seed : PCSRewindSource.RepeatedSeed profile attempts rounds)
    (dimension folds oods queries tail encodedWords : Nat)
    (consumer : ∀ tape : Tape (ParameterBounds.config profile),
      ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
        dimension folds oods queries tail)
    (redundancy : width (ParameterBounds.config profile) < blockLength (ParameterBounds.config profile))
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (admitted : (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).encodedReplyWords ≤ encodedWords) :
    let measured := run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed
    measured.fieldArithmetic + measured.responseCalls + measured.encodedReplyWords +
      originalReservation (ParameterBounds.config profile) lanes attempts family points anchorPoint anchorValue +
      (∑ i, retainedCharge profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed i)) ≤
    totalFieldPolynomial (ParameterBounds.config profile) lanes m points.size attempts rounds dimension folds oods queries tail +
      attempts * ((rounds * streamLength (ParameterBounds.config profile)) * (streamLength (ParameterBounds.config profile) + 1)) +
      encodedWords + originalReservationPolynomial (ParameterBounds.config profile) m points.size attempts +
      attempts * retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes (points.size + 2) := by
  dsimp only
  exact Nat.add_le_add
    (run_total_resource profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed
      dimension folds oods queries tail encodedWords consumer redundancy physicalRoot physicalLanes occupied admitted)
    (all_retained_source_resources profile attempts rounds lanes family points anchorPoint anchorValue prepared
      root strategy seed physicalRoot physicalLanes occupied)

#print axioms run_complete_resource

#print axioms run_total_resource
#print axioms all_retained_source_resources

end Whir.ExtractorArithmeticCostSource
