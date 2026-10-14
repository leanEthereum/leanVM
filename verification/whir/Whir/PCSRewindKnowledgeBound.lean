import Whir.ExtractorArithmeticCostRetained
import Whir.PCSRewindKnowledgeProduction

/-! Concrete production knowledge requirement. Unlike the retired arbitrary
LocalCostModel contract, this uses the actual value-connected source counter
and an input-dependent polynomial. Encoded input/reply allocation and prover
computation are distinct resource units, not silently unit-cost field work. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport ExtractorArithmeticCost
open SamplingProbability AuthenticatedResetProbability
open scoped BigOperators

/-- End-to-end knowledge and efficiency of the legal repeated Root0 extractor
on a fixed dense public instance and adversarial causal strategy. Explains
contains exactly its dense claims, not uncompressed ring-family statements. -/
structure KnowledgeBound (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (error : ℚ) : Prop where
  failure : knowledgeFailureProbability (repeatedExtractor profile attempts rounds)
    ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ ≤ error
  arithmetic : ∀ seed : RepeatedSeed profile attempts rounds,
    let input := ExecutionShapes.Input profile lanes root claims
    (runCounted input strategy (streamLength input.config)
      (attempts * (rounds * streamLength input.config))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)).fieldArithmetic ≤
      totalFieldPolynomial input attempts rounds input.config.logN 6 256 256 input.config.logN
  responses : ∀ seed : RepeatedSeed profile attempts rounds,
    let input := ExecutionShapes.Input profile lanes root claims
    (runRewind input strategy (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program input seed)).responseCalls ≤
      attempts * (rounds * streamLength input.config) * (streamLength input.config + 1)
  records : ∀ seed : RepeatedSeed profile attempts rounds,
    let input := ExecutionShapes.Input profile lanes root claims
    (∑ i, (collectedRecords ⟨input, strategy⟩ (initialLevel profile) (initialDepth profile)
      (seedTapes profile rounds input rfl (seed i))).length) ≤ attempts * (rounds * input.config.queries[0]!)
  counterValue : ∀ seed : RepeatedSeed profile attempts rounds,
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength input.config)
      (attempts * (rounds * streamLength input.config))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    let actual := runRewind input strategy (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program input seed)
    measured.output = actual.output ∧ measured.responseCalls = actual.responseCalls
  strictPrefix : ∀ (historyPrefix : List Batch) (message : Batch)
    (next : Reply → RewindProgram (ParameterBounds.config profile) lanes) (fuel : Nat),
    let input := ExecutionShapes.Input profile lanes root claims
    runRewind input strategy (streamLength input.config) (fuel + 1) (.query historyPrefix message next) =
      if historyPrefix.length ≤ streamLength input.config then
        let actual := runRewind input strategy (streamLength input.config) fuel
          (next (strategy input (replayPast input strategy [] historyPrefix) message))
        ⟨actual.output, actual.responseCalls + historyPrefix.length + 1⟩
      else ⟨none, 0⟩
  verifierValue : ∀ (tape : Tape (ParameterBounds.config profile)) (answers : List Reply),
    let input := ExecutionShapes.Input profile lanes root claims
    (countedAcceptedReplies input tape answers).1 = acceptedReplies input tape answers
  preparationValue : ∀ (seed : RepeatedSeed profile attempts rounds) (i : Fin attempts),
    let input := ExecutionShapes.Input profile lanes root claims
    let retained := retainedRecords profile rounds lanes root claims strategy (seed i)
    (CountedCandidateCheck.countedFilledRecords input retained).1 = filledRecords input retained ∧
    (CountedCandidateCheck.countedReceivedTables input retained).1 =
      Array.ofFn (fun lane : Fin input.lanes =>
        Array.ofFn (fun q : Fin (blockLength input.config) => receivedLane input retained lane q))
  explains : ∀ (seed : RepeatedSeed profile attempts rounds) (w : Witness (ParameterBounds.config profile) lanes),
    let input := ExecutionShapes.Input profile lanes root claims
    (runRewind input strategy (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program input seed)).output = some w → Explains input w
  preparationResources : ∀ (seed : RepeatedSeed profile attempts rounds),
    root.size = blockLength (ParameterBounds.config profile) →
    (∀ row ∈ root.toList, row.size = lanes) →
    (∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN) →
    (∑ i, retainedPreparation profile rounds lanes root claims strategy (seed i)) ≤
      attempts * retainedPreparationPolynomial (ParameterBounds.config profile) rounds lanes claims.size
  admittedResources : ∀ (seed : RepeatedSeed profile attempts rounds) (encodedInputWords : Nat),
    root.size = blockLength (ParameterBounds.config profile) →
    (∀ row ∈ root.toList, row.size = lanes) →
    (∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN) →
    let input := ExecutionShapes.Input profile lanes root claims
    let measured := runCounted input strategy (streamLength input.config)
      (attempts * (rounds * streamLength input.config))
      (countedRepeatedProgram profile rounds input rfl (List.ofFn seed) 0)
    measured.encodedReplyWords + CountedCandidateCheck.consumedWords input [] ≤ encodedInputWords →
    measured.fieldArithmetic + measured.responseCalls +
      (measured.encodedReplyWords + CountedCandidateCheck.consumedWords input []) ≤
      physicalFieldPolynomial (laneCount input.config) lanes (blockLength input.config)
        claims.size input.config.folds.size attempts rounds 6 256 256 input.config.logN +
      attempts * (rounds * streamLength input.config) * (streamLength input.config + 1) + encodedInputWords

/-- Deterministic source properties discharge every efficiency and output
field. Only the independently proved actual failure inequality is composed. -/
theorem knowledgeBound_of_failure (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile)) (error : ℚ)
    (failure : knowledgeFailureProbability (repeatedExtractor profile attempts rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ ≤ error) :
    KnowledgeBound profile attempts rounds lanes root claims strategy error where
  failure := failure
  arithmetic seed := (production_repeated_resources profile rounds attempts lanes root claims strategy seed).1
  responses seed := repeatedExtractor_responseCalls profile attempts rounds ⟨_, strategy⟩ seed
  records seed := production_all_records profile attempts rounds lanes root claims strategy seed
  counterValue seed := actualRepeated_value profile rounds attempts lanes root claims strategy seed
  strictPrefix _ _ _ _ := rfl
  verifierValue _ _ := countedAcceptedReplies_value _ _ _
  preparationValue seed i := retained_preparation_value profile rounds lanes root claims strategy (seed i)
  explains seed w output := repeatedExtractor_output_explains profile attempts rounds lanes root claims strategy seed laneBound w output
  admittedResources seed words rootShape rowShape claimShape admission :=
    production_repeated_physical_resource profile rounds attempts lanes root claims strategy seed words
      rootShape rowShape laneBound claimShape admission
  preparationResources seed rootShape rowShape claimShape := by
    apply production_all_retained_preparation profile rounds attempts lanes root claims strategy seed
      rootShape rowShape laneBound
    intro claim member
    obtain ⟨i, within, equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    have shape : claims[i].weight.size = 2 ^ (ParameterBounds.config profile).logN :=
      claimShape ⟨i, within⟩
    rw [← equal, shape]
    unfold laneCount width
    rw [← Nat.pow_add, Nat.add_sub_of_le (InitialCandidates.production_initial_facts profile).2.1]

/-- Efficient knowledge extraction for every actual source profile above its
rigorously amplified cutoff. The positive acceptance gap determines real
polynomial block fuel. No availability/goodness/certificate premise occurs. -/
theorem production_knowledge_bound (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) (gap : ℝ) (gapPositive : 0 < gap) (security : Nat)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)) :
    KnowledgeBound profile (knowledgeAttempts gap security) (knowledgeRounds profile gap)
      lanes root claims strategy ((1 / 2 : ℚ) ^ security) :=
  knowledgeBound_of_failure profile _ _ lanes root claims strategy laneBound _
    (production_repeated_knowledge_failure profile lanes root claims strategy laneBound
      claimShape claimCap gap gapPositive security advantage)

/-- Universal acceptance-plus-failure form. The zero/negative-gap branch uses
the verifier's actual low acceptance mass; above cutoff the executable bounded
extractor uses inverse-gap fuel and verified-output amplification. The fuel is
an externally parameterized interaction bound, not a runtime computation of
the adversary's acceptance probability. -/
theorem production_universal_knowledge_bound (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) (security : Nat) :
    let κ := probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)
    let gap := κ - (extractionCutoff : ℝ)
    KnowledgeBound profile (knowledgeAttempts gap security) (knowledgeRounds profile gap)
      lanes root claims strategy (extractionCutoff + (1 / 2 : ℚ) ^ security) := by
  dsimp only
  let κ := probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)
  let gap := κ - (extractionCutoff : ℝ)
  apply knowledgeBound_of_failure profile _ _ lanes root claims strategy laneBound
  by_cases high : (extractionCutoff : ℝ) < κ
  · have positive : 0 < gap := sub_pos.mpr high
    have advantage : (extractionCutoff : ℝ) + gap ≤ κ := by dsimp only [gap]; linarith
    have bound := production_repeated_knowledge_failure profile lanes root claims strategy laneBound
      claimShape claimCap gap positive security advantage
    have cutoffNonnegative : (0 : ℚ) ≤ extractionCutoff := by norm_num [extractionCutoff]
    exact bound.trans (by linarith)
  · have bound := knowledge_failure_le_acceptance
      (repeatedExtractor profile (knowledgeAttempts gap security) (knowledgeRounds profile gap))
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩
    have low : κ ≤ (extractionCutoff : ℝ) := le_of_not_gt high
    apply (Rat.cast_le (K := ℝ)).mp
    have powerNonnegative : (0 : ℝ) ≤ ((1 / 2 : ℚ) ^ security : ℝ) := by positivity
    push_cast
    exact (bound.trans low).trans (by linarith)

#print axioms knowledgeBound_of_failure
#print axioms production_knowledge_bound
#print axioms production_universal_knowledge_bound
#check production_knowledge_bound
#check production_universal_knowledge_bound
#print KnowledgeBound
end Whir.PCSRewindExtractor
