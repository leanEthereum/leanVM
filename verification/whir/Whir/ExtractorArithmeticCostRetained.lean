import Whir.PCSRewindKnowledgeResources

/-! Retained-record preparation costs for the actual production prefix collectors. Literal public root, claim and lane guards plus authenticated collected rows discharge the strict consumer contract. Summing all potential attempts also bounds any actual verified-output stopping subset; external prover computation remains outside these resource units. -/
namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck
open scoped BigOperators

set_option maxHeartbeats 4000000

abbrev retainedRecords (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds) :=
  let input := ExecutionShapes.Input profile lanes root claims
  baseRecords (collectedRecords ⟨input, strategy⟩ (initialLevel profile) (initialDepth profile)
    (seedTapes profile rounds input rfl seed))

/-- No acceptance-to-resource inference: authentication identifies every retained row with a bounded literal public row. -/
theorem retained_consumer (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (physicalClaims : ∀ claim ∈ claims.toList,
      claim.weight.size = laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile)) :
    let input := ExecutionShapes.Input profile lanes root claims
    ConsumerInput input (rounds * input.config.queries[0]!) claims.size
      (retainedRecords profile rounds lanes root claims strategy seed) := by
  dsimp only
  have facts := InitialCandidates.production_initial_facts profile
  refine ⟨facts.2.1, facts.2.2.1, occupied, ?_, ?_, le_rfl, physicalClaims,
    physicalRoot, physicalLanes⟩
  · exact (List.length_filterMap_le _ _).trans
      (production_collected_records profile rounds lanes root claims strategy seed)
  · intro record member
    have authenticated := collected_base_authenticated profile lanes root claims strategy
      (seedTapes profile rounds (ExecutionShapes.Input profile lanes root claims) rfl seed)
    rw [authenticated record member]
    have within : record.1.val < root.size := by
      rw [physicalRoot]
      exact record.1.isLt
    rw [getElem!_pos root record.1.val within]
    exact physicalLanes _ (Array.getElem_mem_toList within)

/-- Actual filled-record lookup and received-lane table values on the actual accepted full-suffix collector. -/
theorem retained_preparation_value (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    let records := retainedRecords profile rounds lanes root claims strategy seed
    (countedFilledRecords input records).1 = filledRecords input records ∧
    (countedReceivedTables input records).1 = Array.ofFn (fun lane : Fin input.lanes =>
      Array.ofFn (fun q : Fin (blockLength input.config) => receivedLane input records lane q)) := by
  exact ⟨countedFilledRecords_value _ _, countedReceivedTables_value _ _⟩

/-- Separately charged lookup visits, materialized received slots and admitted public/retained words. -/
def retainedPreparation (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds) : Nat :=
  let input := ExecutionShapes.Input profile lanes root claims
  let records := retainedRecords profile rounds lanes root claims strategy seed
  (countedReceivedTables input records).2 + consumedWords input records

def retainedPreparationPolynomial (c : Config) (rounds lanes claims : Nat) : Nat :=
  blockLength c * (rounds * c.queries[0]!) + lanes * blockLength c +
    publicHeaderWords c + blockLength c * (lanes + 1) +
    claims * (3 * laneCount c * width c + 4) + rounds * c.queries[0]! * (lanes + 2)

theorem production_retained_preparation (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (physicalClaims : ∀ claim ∈ claims.toList,
      claim.weight.size = laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile)) :
    retainedPreparation profile rounds lanes root claims strategy seed ≤
      retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes claims.size := by
  exact admitted_preparation_resource (ExecutionShapes.Input profile lanes root claims)
    (retainedRecords profile rounds lanes root claims strategy seed) _ _
    (retained_consumer profile rounds lanes root claims strategy seed physicalRoot physicalLanes
      occupied physicalClaims)

/-- Every potential prefix is bounded, including withholding and rejected trials; any actual stopping subset is therefore bounded by the same attempt polynomial. -/
theorem production_retained_preparation_subset (profile : ParameterBounds.Profile)
    (rounds attempts lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) (visited : Finset (Fin attempts))
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (physicalClaims : ∀ claim ∈ claims.toList,
      claim.weight.size = laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile)) :
    (∑ i ∈ visited, retainedPreparation profile rounds lanes root claims strategy (seed i)) ≤
      attempts * retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes claims.size := by
  have card : visited.card ≤ attempts := by
    simpa using Finset.card_le_card (Finset.subset_univ visited)
  calc
    _ ≤ ∑ _i ∈ visited,
        retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes claims.size :=
      Finset.sum_le_sum (fun i _ => production_retained_preparation profile rounds lanes root claims
        strategy (seed i) physicalRoot physicalLanes occupied physicalClaims)
    _ = visited.card * retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes claims.size := by
      simp
    _ ≤ _ := Nat.mul_le_mul_right _ card

theorem production_all_retained_preparation (profile : ParameterBounds.Profile)
    (rounds attempts lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (occupied : lanes ≤ laneCount (ParameterBounds.config profile))
    (physicalClaims : ∀ claim ∈ claims.toList,
      claim.weight.size = laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile)) :
    (∑ i, retainedPreparation profile rounds lanes root claims strategy (seed i)) ≤
      attempts * retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes claims.size := by
  simpa using production_retained_preparation_subset profile rounds attempts lanes root claims
    strategy seed Finset.univ physicalRoot physicalLanes occupied physicalClaims

#print axioms retained_consumer
#print axioms retained_preparation_value
#print axioms production_all_retained_preparation
#print axioms production_retained_preparation_subset

end Whir.ExtractorArithmeticCost
