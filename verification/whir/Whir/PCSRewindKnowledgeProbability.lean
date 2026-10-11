import Whir.PCSRewindExtractorAttempts

/-! Probability laws for the executable repeated extractor. The failure event
is actual runRewind failure, not an auxiliary first-verified observer. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction
open SamplingProbability AuthenticatedResetProbability ResetAcceptanceAmplification

set_option maxHeartbeats 2000000

/-- Explicit composition breaks instance search at the deeply nested dependent
tape, without introducing any executable field enumeration. -/
noncomputable instance repeatedSeedFintype (profile : ParameterBounds.Profile) (attempts rounds : Nat) :
    Fintype (RepeatedSeed profile attempts rounds) := by
  letI : Fintype (Seed profile rounds) := inferInstanceAs
    (Fintype (Tape (ParameterBounds.config profile) × (Fin rounds → TrialSeed profile)))
  exact inferInstanceAs (Fintype (Fin attempts → Seed profile rounds))

theorem firstOutput_none_iff {α : Type*} (outputs : List (Option α)) :
    firstOutput outputs = none ↔ ∀ output ∈ outputs, output = none := by
  induction outputs with
  | nil => simp [firstOutput]
  | cons output rest ih => cases output <;> simp [firstOutput, ih]

/-- Soundness of the actual stop rule identifies successful execution with an
explaining output, for every seed and every adversarial strategy. -/
theorem extractionSuccess_iff_output (profile : ParameterBounds.Profile)
    (rounds lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (seed : Seed profile rounds) :
    extractionSuccess (extractor profile rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ seed ↔
      (runRewind (ExecutionShapes.Input profile lanes root claims) strategy
        (extractor profile rounds).maxReplay (extractor profile rounds).rewindRounds
        ((extractor profile rounds).program (ExecutionShapes.Input profile lanes root claims) seed)).output ≠ none := by
  constructor
  · rintro ⟨w, output, _⟩; simp [output]
  · intro output
    obtain ⟨w, equal⟩ := Option.ne_none_iff_exists'.mp output
    exact ⟨w, equal, extractor_output_explains profile rounds lanes root claims strategy seed laneBound w equal⟩

/-- Every attempt has fresh full prefix/suffix product randomness. Stopping
short on success preserves the all-attempts-fail event exactly. -/
theorem repeatedExtractor_failure_iff (profile : ParameterBounds.Profile)
    (attempts rounds lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (seed : RepeatedSeed profile attempts rounds) :
    ¬ extractionSuccess (repeatedExtractor profile attempts rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ seed ↔
    ∀ i, ¬ extractionSuccess (extractor profile rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (seed i) := by
  have actual : extractionSuccess (repeatedExtractor profile attempts rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ seed ↔
      (runRewind (ExecutionShapes.Input profile lanes root claims) strategy
        (repeatedExtractor profile attempts rounds).maxReplay (repeatedExtractor profile attempts rounds).rewindRounds
        ((repeatedExtractor profile attempts rounds).program (ExecutionShapes.Input profile lanes root claims) seed)).output ≠ none := by
    constructor
    · rintro ⟨w, output, _⟩; simp [output]
    · intro output
      obtain ⟨w, equal⟩ := Option.ne_none_iff_exists'.mp output
      exact ⟨w, equal, repeatedExtractor_output_explains profile attempts rounds lanes root claims strategy seed laneBound w equal⟩
  rw [actual, not_not, repeatedExtractor_output, firstOutput_none_iff, List.forall_mem_ofFn_iff]
  simp only [extractionSuccess_iff_output profile rounds lanes root claims strategy laneBound, not_not]

/-- The concrete machine inherits independent-attempt amplification. Its
single-attempt success lower bound is instantiated by the production heavy
certificate; it is not a prover-availability hypothesis. -/
theorem repeatedExtractor_failure_probability (profile : ParameterBounds.Profile)
    (attempts rounds lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (chance : ℝ) (chanceNonneg : 0 ≤ chance)
    (lower : chance ≤ probability (extractionSuccess (extractor profile rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩)) :
    probability (fun seed => ¬ extractionSuccess (repeatedExtractor profile attempts rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ seed) ≤ (1 - chance) ^ attempts := by
  have bound := repeated_extraction_failure (extractor profile rounds)
    ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ chance chanceNonneg lower attempts
  convert bound using 1
  congr 1
  funext seed
  exact propext (repeatedExtractor_failure_iff profile attempts rounds lanes root claims strategy laneBound seed)

/-- In the low-acceptance branch, the joint knowledge failure is bounded by
the actual causal verifier acceptance mass, regardless of extraction output. -/
theorem knowledge_failure_le_acceptance {S : Type*} [Fintype S] [Nonempty S]
    (machine : Extractor S) (prover : CommittedProver) :
    (knowledgeFailureProbability machine prover : ℝ) ≤
      probability (fun tape => experiment prover.input prover.respond tape = true) := by
  classical
  have included := mono
    (fun sample : Tape prover.input.config × S =>
      experiment prover.input prover.respond sample.1 = true ∧ ¬ extractionSuccess machine prover sample.2)
    (fun sample => experiment prover.input prover.respond sample.1 = true)
    (fun _ accepted => accepted.1)
  have product := product_left (B := S)
    (fun tape : Tape prover.input.config => experiment prover.input prover.respond tape = true)
  rw [product] at included
  rw [probability_eq_uniformProb] at included
  exact included

/-- The acceptance-plus-failure game uses independent verifier and extraction
randomness. This bound is about the actual knowledgeFailureProbability. -/
theorem repeatedExtractor_knowledge_failure (profile : ParameterBounds.Profile)
    (attempts rounds lanes : Nat) (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (chance : ℝ) (chanceNonneg : 0 ≤ chance)
    (lower : chance ≤ probability (extractionSuccess (extractor profile rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩)) :
    (knowledgeFailureProbability (repeatedExtractor profile attempts rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ : ℝ) ≤ (1 - chance) ^ attempts := by
  classical
  let prover : CommittedProver := ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩
  have included := mono
    (fun sample : Tape prover.input.config × RepeatedSeed profile attempts rounds =>
      experiment prover.input prover.respond sample.1 = true ∧
        ¬ extractionSuccess (repeatedExtractor profile attempts rounds) prover sample.2)
    (fun sample => ¬ extractionSuccess (repeatedExtractor profile attempts rounds) prover sample.2)
    (fun _ accepted => accepted.2)
  have product := product_left (B := Tape prover.input.config)
    (fun seed => ¬ extractionSuccess (repeatedExtractor profile attempts rounds) prover seed)
  have swapped := SamplingProbability.probability_equiv (Equiv.prodComm _ _)
    (fun sample : RepeatedSeed profile attempts rounds × Tape prover.input.config =>
      ¬ extractionSuccess (repeatedExtractor profile attempts rounds) prover sample.1)
  change probability (fun sample : Tape prover.input.config × RepeatedSeed profile attempts rounds =>
      ¬ extractionSuccess (repeatedExtractor profile attempts rounds) prover sample.2) =
    probability (fun sample : RepeatedSeed profile attempts rounds × Tape prover.input.config =>
      ¬ extractionSuccess (repeatedExtractor profile attempts rounds) prover sample.1) at swapped
  rw [swapped, product] at included
  rw [probability_eq_uniformProb] at included
  exact included.trans (repeatedExtractor_failure_probability profile attempts rounds lanes root claims strategy laneBound chance chanceNonneg lower)

#print axioms repeatedExtractor_failure_probability
#print axioms repeatedExtractor_knowledge_failure
end Whir.PCSRewindExtractor
