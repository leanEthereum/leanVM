import Whir.PCSRewindKnowledgeCollector
import Whir.PCSRewindKnowledgeParameters

/-! Full independent suffix samples drive the actual collector. The failure
probability here refers to runRewind extractionSuccess, after every live lane
and all original claims are checked. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability AuthenticatedResetSupport
open SupportedCandidateRecovery ResetAcceptanceAmplification

set_option maxHeartbeats 4000000

/-- A proved heavy witness plus actual acceptance-dependent coverage gives a
conditional success probability for the REAL bounded rewind program. -/
theorem conditional_extractor_success (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (bad : Tape (ParameterBounds.config profile) → Prop) (base : Tape (ParameterBounds.config profile))
    (η : ℝ) (ηnonnegative : 0 ≤ η) (ηleOne : η ≤ 1)
    (large : (heavyQueryLoss profile : ℝ) + blockLength (ParameterBounds.config profile) * η <
      probability (safeResetAccept profile lanes root claims strategy bad base))
    (certificate : HeavyWitness profile lanes root claims
      (heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
        (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
        (safeResetAccept profile lanes root claims strategy bad base) η)) :
    1 - blockLength (ParameterBounds.config profile) * (1 - η) ^ rounds ≤
      probability (fun seed : Fin rounds → TrialSeed profile => extractionSuccess (extractor profile rounds)
        ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (base, seed)) := by
  let covered := CoversHeavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy bad base) η rounds
  have failure := coverage_failure_le (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy bad base) η ηnonnegative ηleOne rounds
  have chance : 1 - blockLength (ParameterBounds.config profile) * (1 - η) ^ rounds ≤ probability covered := by
    have total := complement covered
    linarith
  exact chance.trans (mono covered _ (fun seed coverage =>
    extractor_success_of_safe_coverage profile rounds lanes root claims strategy laneBound bad base
      η ηnonnegative large certificate seed coverage))

/-- The real inverse-availability collector blocks reduce conditional failure
below one quarter, with optional further independent security blocks. -/
theorem conditional_extractor_schedule (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (bad : Tape (ParameterBounds.config profile) → Prop) (base : Tape (ParameterBounds.config profile))
    (η : ℝ) (ηpositive : 0 < η) (ηleOne : η ≤ 1) (block security : Nat)
    (enough : 1 ≤ (block : ℝ) * η)
    (large : (heavyQueryLoss profile : ℝ) + blockLength (ParameterBounds.config profile) * η <
      probability (safeResetAccept profile lanes root claims strategy bad base))
    (certificate : HeavyWitness profile lanes root claims
      (heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
        (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
        (safeResetAccept profile lanes root claims strategy bad base) η)) :
    1 - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ security ≤
      probability (fun seed : Fin (collectorRounds block (initialDepth profile) security) → TrialSeed profile =>
        extractionSuccess (extractor profile (collectorRounds block (initialDepth profile) security))
          ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (base, seed)) := by
  let rounds := collectorRounds block (initialDepth profile) security
  let covered := CoversHeavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy bad base) η rounds
  have failure := collector_schedule_failure (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy bad base) η ηpositive ηleOne block security enough
  have chance : 1 - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ security ≤ probability covered := by
    have total := complement covered
    linarith
  exact chance.trans (mono covered _ (fun seed coverage =>
    extractor_success_of_safe_coverage profile rounds lanes root claims strategy laneBound bad base
      η ηpositive.le large certificate seed coverage))

#print axioms conditional_extractor_success
#print axioms conditional_extractor_schedule
end Whir.PCSRewindExtractor
