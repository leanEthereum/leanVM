import Whir.PCSRewindKnowledgeHeavy

/-! The legal full-trial collector recovers and verifies the SAME witness from
its heavy-coordinate certificate. The safe predicate is proof-only: the
collector's executable program tests ordinary verifier acceptance only. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability AuthenticatedResetSupport
open SupportedCandidateRecovery ResetAcceptanceAmplification

set_option maxHeartbeats 4000000
attribute [local irreducible] ParameterBounds.config

/-- The subset used to analyze the actual collector. -/
def safeResetAccept (profile : ParameterBounds.Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy)
    (bad : Tape (ParameterBounds.config profile) → Prop)
    (base : Tape (ParameterBounds.config profile)) (trial : TrialSeed profile) : Prop :=
  let tape := fullResetTape (ExecutionShapes.Input profile lanes root claims) base
    (initialLevel profile) (initialDepth profile) (initialChunks profile) trial.1 trial.2
  experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true ∧ ¬ bad tape

set_option maxRecDepth 100000 in
/-- Exact uniform law for prefix plus independent full reset suffix, applied
to the arbitrary SAFE acceptance predicate, not just coordinate events. -/
theorem safeResetAccept_probability (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (bad : Tape (ParameterBounds.config profile) → Prop) :
    probability (fun draw : Tape (ParameterBounds.config profile) × TrialSeed profile =>
      safeResetAccept profile lanes root claims strategy bad draw.1 draw.2) =
    probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true ∧ ¬ bad tape) := by
  unfold safeResetAccept
  exact fullResetTape_probability (ExecutionShapes.Input profile lanes root claims)
    (initialLevel profile) (initialDepth profile) (initialChunks profile)
    (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true ∧ ¬ bad tape)

/-- A production certificate carries a single explaining witness and the
actual common Root0 coordinates. Its radius is derived below from safe mass. -/
structure HeavyWitness (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (H : Finset (Fin (blockLength (ParameterBounds.config profile)))) where
  witness : Witness (ParameterBounds.config profile) lanes
  explains : Explains (ExecutionShapes.Input profile lanes root claims) witness
  matching : ∀ q ∈ H, rowMatches (ParameterBounds.config profile) lanes
    (encodedLanes (ParameterBounds.config profile) (paddedWitness (ParameterBounds.config profile) lanes witness))
    (q, root[q.val]!) = true

/-- Complete actual collectAcceptedProgram → all live Gao lanes → common
coordinate and ALL original claim checks → explaining verified output. -/
theorem extractor_success_of_safe_coverage (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (bad : Tape (ParameterBounds.config profile) → Prop)
    (base : Tape (ParameterBounds.config profile))
    (η : ℝ) (nonnegative : 0 ≤ η)
    (large : (heavyQueryLoss profile : ℝ) + blockLength (ParameterBounds.config profile) * η <
      probability (safeResetAccept profile lanes root claims strategy bad base))
    (certificate : HeavyWitness profile lanes root claims
      (heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
        (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
        (safeResetAccept profile lanes root claims strategy bad base) η))
    (seed : Fin rounds → TrialSeed profile)
    (coverage : CoversHeavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
      (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
      (safeResetAccept profile lanes root claims strategy bad base) η rounds seed) :
    extractionSuccess (extractor profile rounds)
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (base, seed) := by
  let input := ExecutionShapes.Input profile lanes root claims
  let tapes := seedTapes profile rounds input rfl (base, seed)
  let extensionRecords := collectedRecords ⟨input, strategy⟩ (initialLevel profile) (initialDepth profile) tapes
  let records := baseRecords extensionRecords
  let H := heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy bad base) η
  have embedded : ∀ record ∈ extensionRecords, record.2 = (root[record.1.val]!).map E.ofK :=
    collected_initial_embedded profile lanes root claims strategy tapes
  have authenticated : ∀ record ∈ records, record.2 = root[record.1.val]! :=
    collected_base_authenticated profile lanes root claims strategy tapes
  have coveredExtension : ∀ q ∈ H, ∃ record ∈ extensionRecords, record.1 = q :=
    safe_collector_covers profile rounds lanes root claims strategy base _
      (fun trial accepted => accepted.1) η seed coverage
  have covered : ∀ q ∈ H, ∃ record ∈ records, record.1 = q :=
    fun q member => baseRecords_covers root extensionRecords embedded q (coveredExtension q member)
  have sizes := production_heavy_size profile _ η nonnegative large
  have decoded := decodeAndCheck_of_heavy input records
    (InitialCandidates.production_initial_facts profile).2.2.1
    (InitialCandidates.production_initial_facts profile).2.1 laneBound
    (production_heavy_static profile).2.1 authenticated H covered sizes.1 sizes.2 certificate.witness
    (fun q member lane => live_agrees_of_rowMatches input
      (InitialCandidates.production_initial_facts profile).2.1 laneBound certificate.witness q
      (certificate.matching q member) lane)
    certificate.matching certificate.explains.2
  refine ⟨certificate.witness, ?_, certificate.explains⟩
  rw [extractor_run]
  exact decoded

#print axioms safeResetAccept_probability
#print axioms extractor_success_of_safe_coverage
end Whir.PCSRewindExtractor
