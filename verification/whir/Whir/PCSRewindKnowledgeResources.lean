import Whir.ExtractorArithmeticCostPolynomial
import Whir.PCSRewindKnowledgeHeavy

/-! Source-derived resource guards for all production profiles. The arithmetic
counter is value-connected to the actual repeated run, including rejected
trials and every replay. Prover runtime and raw reply allocation are not field
arithmetic: callers must charge their encoded consumed input/reply lengths. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport ExtractorArithmeticCost
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem production_challenge_static : ∀ p : ParameterBounds.Profile,
    (ParameterBounds.config p).logN ≤ 64 ∧
    (∀ i : Fin (ParameterBounds.config p).folds.size,
      (ParameterBounds.config p).folds[i.val]! ≤ (ParameterBounds.config p).logN ∧
      (ParameterBounds.config p).folds[i.val]! ≤ 6 ∧
      oodCount (ParameterBounds.config p) i.val ≤ 256 ∧
      (ParameterBounds.config p).queries[i.val]! ≤ 256) := by
  decide +kernel

/-- Generated source tapes meet the cost consumer guards even when the prover
returns malformed or withholding replies. No answer-shape goodness is needed. -/
theorem production_challenge_input (profile : ParameterBounds.Profile)
    (tape : Tape (ParameterBounds.config profile)) :
    ChallengeInput (ParameterBounds.config profile) (challenges (ParameterBounds.config profile) tape)
      (ParameterBounds.config profile).logN 6 256 256 (ParameterBounds.config profile).logN := by
  let c := ParameterBounds.config profile
  have stat := production_challenge_static profile
  refine ⟨le_rfl, stat.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i within
    simpa [challenges, getElem!_pos, within] using (stat.2 ⟨i, within⟩).1
  · intro i within
    simpa [challenges, getElem!_pos, within] using (stat.2 ⟨i, within⟩).2.1
  · intro i within
    simpa [challenges, getElem!_pos, within] using (stat.2 ⟨i, within⟩).2.2.1
  · intro i within point member
    simp only [challenges, getElem!_pos, Array.size_ofFn, within, Array.getElem_ofFn,
      Array.toList_ofFn, List.mem_ofFn] at member
    obtain ⟨j, rfl⟩ := member
    simp only [Array.size_ofFn]
    exact Nat.sub_le _ _
  · intro i within
    exact (stat.2 ⟨i, within⟩).2.2.2
  · simp [challenges]
  · simp [challenges]

/-- Whole repeated machine field arithmetic and actual black-box response calls,
with every source consumer hypothesis discharged for the production family. -/
theorem production_repeated_resources (profile : ParameterBounds.Profile)
    (rounds attempts lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength (ParameterBounds.config profile))
      (attempts * (rounds * streamLength (ParameterBounds.config profile)))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    measured.fieldArithmetic ≤ totalFieldPolynomial input attempts rounds
      input.config.logN 6 256 256 input.config.logN ∧
      measured.responseCalls ≤ attempts * (rounds * streamLength input.config) * (streamLength input.config + 1) :=
  actualRepeated_cost profile rounds attempts lanes root claims strategy seed _ 6 256 256 _
    (production_challenge_input profile) (production_heavy_static profile).2.1

/-- Every actual prefix collector retains at most rounds·queries records.
Rejected trials contribute zero. Base projection only decreases this count. -/
theorem production_collected_records (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    (collectedRecords ⟨input, strategy⟩ (initialLevel profile) (initialDepth profile)
      (seedTapes profile rounds input rfl seed)).length ≤ rounds * input.config.queries[0]! := by
  dsimp only
  have bound := collectedRecords_length_le
    ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (initialLevel profile) (initialDepth profile)
    (seedTapes profile rounds (ExecutionShapes.Input profile lanes root claims) rfl seed)
  simpa [seedTapes, initialLevel] using bound

/-- Summing all potential prefix collectors upper-bounds records for any actual
verified-output stopping prefix; the machine never retries a successful one. -/
theorem production_all_records (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    (∑ i, (collectedRecords ⟨input, strategy⟩ (initialLevel profile) (initialDepth profile)
      (seedTapes profile rounds input rfl (seed i))).length) ≤
      attempts * (rounds * input.config.queries[0]!) := by
  dsimp only
  calc
    _ ≤ ∑ _ : Fin attempts, rounds * (ParameterBounds.config profile).queries[0]! :=
      Finset.sum_le_sum (fun i _ => production_collected_records profile rounds lanes root claims strategy (seed i))
    _ = _ := by simp

/-- Measured arithmetic, every actual replay response, and admitted encoded
input/reply words compose in literal resource units. U is charged, not assumed
to be free; the prover's internal computation remains outside this boundary. -/
theorem production_repeated_physical_resource (profile : ParameterBounds.Profile)
    (rounds attempts lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) (encodedInputWords : Nat)
    (physicalRoot : root.size = blockLength (ParameterBounds.config profile))
    (physicalLanes : ∀ row ∈ root.toList, row.size = lanes)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (admittedInput :
      let input := ExecutionShapes.Input profile lanes root claims
      let measured := runCounted input strategy (streamLength input.config)
        (attempts * (rounds * streamLength input.config))
        (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
      measured.encodedReplyWords + CountedCandidateCheck.consumedWords input [] ≤ encodedInputWords) :
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength input.config)
      (attempts * (rounds * streamLength input.config))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    measured.fieldArithmetic + measured.responseCalls +
      (measured.encodedReplyWords + CountedCandidateCheck.consumedWords input []) ≤
      physicalFieldPolynomial (laneCount input.config) lanes (blockLength input.config)
        claims.size input.config.folds.size attempts rounds 6 256 256 input.config.logN +
      attempts * (rounds * streamLength input.config) * (streamLength input.config + 1) +
      encodedInputWords := by
  have fullWidth : laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile) =
      2 ^ (ParameterBounds.config profile).logN := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (InitialCandidates.production_initial_facts profile).2.1]
  have physicalClaims : ∀ claim ∈ claims.toList,
      claim.weight.size = laneCount (ParameterBounds.config profile) * width (ParameterBounds.config profile) := by
    intro claim member
    obtain ⟨j, within, equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    rw [← equal, fullWidth]
    exact claimShape ⟨j, within⟩
  exact actualRepeated_total_resource profile rounds attempts lanes root claims strategy seed
    6 256 256 (ParameterBounds.config profile).logN encodedInputWords
    (production_challenge_input profile) (production_heavy_static profile).2.1
    physicalRoot physicalLanes laneBound physicalClaims admittedInput

#print axioms production_challenge_input
#print axioms production_repeated_resources
#print axioms production_all_records
#print axioms production_repeated_physical_resource
end Whir.PCSRewindExtractor
