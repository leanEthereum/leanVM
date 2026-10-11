import Whir.PCSRewindKnowledgeSuccess
import Whir.SupportedCandidateProtocolProbability
import Whir.SupportedCandidateProtocolAccepted

/-! The production safe event is the DERIVED causal/fold/cancellation/collision
ledger. Acceptance supplies safe-prefix mass and heavy support; no prover
availability or fixed-target proximity is assumed. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability AuthenticatedResetSupport
open ResetAcceptanceAmplification

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] ParameterBounds.config

noncomputable def productionBad (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) :=
  SupportedCandidateProtocol.KnowledgeBad profile lanes root claims strategy

/-- The actual source ledger, including separately charged SAME-candidate
fold claim escape and row cancellation, supplies the whole bad-event budget. -/
theorem production_bad_probability (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) :
    probability (productionBad profile lanes root claims strategy) ≤ (knowledgeBadEnvelope : ℝ) := by
  classical
  rw [probability_eq_uniformProb]
  apply Rat.cast_le.mpr
  exact (SupportedCandidateProtocol.knowledgeBad_probability profile lanes root claims strategy laneBound claimShape).trans
    (SupportedCandidateProtocol.production_knowledgeLedger profile claims.size claimCap)

/-- Exact prefix/fullReset product law and the actual bad-event budget derive
safe accepted mass from the causal verifier's true acceptance probability. -/
theorem production_safe_mass (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) :
    probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true) -
      (knowledgeBadEnvelope : ℝ) ≤
    probability (fun draw : Tape (ParameterBounds.config profile) × TrialSeed profile =>
      safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) draw.1 draw.2) := by
  rw [safeResetAccept_probability]
  have safe := safe_acceptance_mass
    (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)
    (productionBad profile lanes root claims strategy)
  have bad := production_bad_probability profile lanes root claims strategy laneBound claimShape claimCap
  linarith

/-- The κ/2 loss is fully accounted for BEFORE Gao heavy support is derived. -/
theorem production_good_prefix_heavy_mass (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) (gap : ℝ) (gapPositive : 0 < gap)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true))
    (base : Tape (ParameterBounds.config profile))
    (good : GoodPrefix (fun draw : Tape (ParameterBounds.config profile) × TrialSeed profile =>
      safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) draw.1 draw.2) base) :
    (heavyQueryLoss profile : ℝ) + blockLength (ParameterBounds.config profile) * heavyAvailability profile gap <
      probability (safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base) := by
  have mass := production_safe_mass profile lanes root claims strategy laneBound claimShape claimCap
  have conditional := good
  change probability _ / 2 ≤ probability _ at conditional
  have cutoff : (2 * heavyQueryLoss profile + knowledgeBadEnvelope : ℚ) < extractionCutoff := by
    linarith [production_amplified_cutoff profile]
  have cutoffReal : (2 * (heavyQueryLoss profile : ℝ) + knowledgeBadEnvelope) < extractionCutoff := by
    exact_mod_cast cutoff
  have scale : (blockLength (ParameterBounds.config profile) : ℝ) * heavyAvailability profile gap = gap / 4 := by
    unfold heavyAvailability
    push_cast
    field_simp [show (blockLength (ParameterBounds.config profile) : ℝ) ≠ 0 by positivity]
  rw [scale]
  linarith

/-- Conversion from the stratified collector seed to the actual indivisible
query/lambda challenge message. The casts change only the index proof. -/
def resetDraw (profile : ParameterBounds.Profile) (trial : TrialSeed profile) :
    CausalProbability.Sample (.query (SupportedCandidateProtocol.initialLevel profile)) :=
  ((fun j => trial.1 (Fin.cast (initialChunks profile) j)), trial.2.1)

theorem resetDraw_squeezes (profile : ParameterBounds.Profile) (trial : TrialSeed profile) :
    Array.ofFn (resetDraw profile trial).1 = Array.ofFn trial.1 := by
  apply Array.ext
  · simp only [Array.size_ofFn]
    exact initialChunks profile
  · intro i hi hj
    simp [resetDraw, Fin.cast]

/-- Every safe accepted full reset hits one prefix-fixed scalar agreement set
under the EXACT collector query law, even with adversarial later replies. -/
theorem safeReset_hits (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (base : Tape (ParameterBounds.config profile)) (target : Array E)
    (matching : RewindBatchTarget.Target
      (CausalExecution.followingCandidates (ExecutionShapes.Input profile lanes root claims) strategy base 0)
      (challenges (ParameterBounds.config profile) base).levels[0]!.oodPoints[0]!
      (CausalExecution.proof (ExecutionShapes.Input profile lanes root claims) strategy base).levels[0]!.oods[0]!.value target)
    (separated : LevelBoundary.Separated
      (CausalExecution.followingCandidates (ExecutionShapes.Input profile lanes root claims) strategy base 0)
      (challenges (ParameterBounds.config profile) base).levels[0]!.oodPoints[0]!)
    (trial : TrialSeed profile)
    (accepted : safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base trial) :
    ∀ i, RewindCoverage.sampledPosition (initialDepth profile) (ParameterBounds.config profile).queries[0]!
      (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1 trial.1 i ∈
      LevelBoundary.agreeingColumns ((ParameterBounds.config profile).logN - (ParameterBounds.config profile).folds[0]!)
        (ParameterBounds.config profile).rates[0]! target
        (QueryBatchSoundness.oldWord ((ParameterBounds.config profile).logN - (ParameterBounds.config profile).folds[0]!)
          (ParameterBounds.config profile).rates[0]! (liftRoot root) true
          (challenges (ParameterBounds.config profile) base).levels[0]!.folds) := by
  have hit := SupportedCandidateProtocol.accepted_safe_hits profile lanes root claims strategy
    base trial.2.2 (resetDraw profile trial) target matching separated accepted.1 accepted.2
  obtain ⟨qs, derived, agrees⟩ := hit
  have squeezed := congrArg
    (deriveQueries (remaining (ParameterBounds.config profile) 0 + (ParameterBounds.config profile).rates[0]!)
      (ParameterBounds.config profile).queries[0]!)
    (resetDraw_squeezes profile trial)
  have derived' := squeezed.symm.trans derived
  have hit' : SamplingProbability.allQueriesHit (initialDepth profile)
      (ParameterBounds.config profile).queries[0]!
      (LevelBoundary.agreeingColumns ((ParameterBounds.config profile).logN - (ParameterBounds.config profile).folds[0]!)
        (ParameterBounds.config profile).rates[0]! target
        (QueryBatchSoundness.oldWord ((ParameterBounds.config profile).logN - (ParameterBounds.config profile).folds[0]!)
          (ParameterBounds.config profile).rates[0]! (liftRoot root) true
          (challenges (ParameterBounds.config profile) base).levels[0]!.folds)) trial.1 := by
    unfold SamplingProbability.allQueriesHit
    refine ⟨qs, ?_, ?_⟩
    · simpa only [(InitialCandidates.production_initial_facts profile).1] using derived'
    · exact Eq.mp (congrArg (fun n =>
        ∀ i : Fin (ParameterBounds.config profile).queries[0]!, qs[i.val]! ∈
          (LevelBoundary.agreeingColumns n (ParameterBounds.config profile).rates[0]! target
            (QueryBatchSoundness.oldWord n (ParameterBounds.config profile).rates[0]!
              (liftRoot root) true (challenges (ParameterBounds.config profile) base).levels[0]!.folds)).image
            (@Fin.val (2 ^ (n + (ParameterBounds.config profile).rates[0]!))))
        (InitialCandidates.production_initial_facts profile).1) agrees
  exact (allQueriesHit_iff (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1 _ trial.1).mp hit'

/-- Production SAME-K-w heavy certificate: existence, every dense input Claim,
and common-coordinate agreement are derived from actual safe acceptance. -/
theorem production_heavy_witness (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (base : Tape (ParameterBounds.config profile))
    (η : ℝ) (ηpositive : 0 < η)
    (large : (heavyQueryLoss profile : ℝ) + blockLength (ParameterBounds.config profile) * η <
      probability (safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base)) :
    Nonempty (HeavyWitness profile lanes root claims
      (heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
        (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
        (safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base) η)) := by
  classical
  have lossNonnegative : (0 : ℝ) ≤ (heavyQueryLoss profile : ℝ) := by
    unfold heavyQueryLoss
    positivity
  have acceptedExists : ∃ trial, safeResetAccept profile lanes root claims strategy
      (productionBad profile lanes root claims strategy) base trial := by
    by_contra absent
    have no := not_exists.mp absent
    have empty : safeResetAccept profile lanes root claims strategy
        (productionBad profile lanes root claims strategy) base = (fun _ => False) := by
      funext trial
      exact propext ⟨no trial, False.elim⟩
    rw [empty] at large
    have zero : probability (fun _ : TrialSeed profile => False) = 0 := by simp [probability]
    rw [zero] at large
    have lightNonnegative : (0 : ℝ) ≤ blockLength (ParameterBounds.config profile) * η := by positivity
    linarith
  obtain ⟨trial, accepted⟩ := acceptedExists
  obtain ⟨target, matching, separated, size, truth, prior, valid, laneBound⟩ :=
    SupportedCandidateProtocol.accepted_safe_target profile lanes root claims strategy base trial.2.2
      (resetDraw profile trial) accepted.1 accepted.2
  let H := heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base) η
  have included := heavy_subset_of_safe_hits (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    (safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) base)
    η ηpositive _ (safeReset_hits profile lanes root claims strategy base target matching separated)
  have sizes := production_heavy_size profile _ η ηpositive.le large
  obtain ⟨w, explains, rows⟩ := SupportedCandidateProtocol.same_w_on_support profile lanes root claims strategy
    base valid laneBound (fun j => (prior.1 j).1) (fun j => (prior.1 j).2)
    prior.2.1 prior.2.2 target size truth H sizes.2 (by
      intro q member
      exact (Finset.mem_filter.mp (included member)).2)
  exact ⟨⟨w, explains, rows⟩⟩

/-- A fresh actual prefix and polynomial full-reset collection have verified
success chance at least gap/4. No certificate, availability or goodness is a
theorem premise: the production SAME-w certificate is derived internally. -/
theorem production_single_attempt_chance (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) (gap : ℝ) (gapPositive : 0 < gap)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)) :
    gap / 4 ≤ probability (extractionSuccess (extractor profile (knowledgeRounds profile gap))
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩) := by
  classical
  have acceptanceLeOne := le_one
    (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)
  have cutoffNonnegative : (0 : ℝ) ≤ (extractionCutoff : ℝ) := by
    norm_num [extractionCutoff]
  have gapLeOne : gap ≤ 1 := by linarith
  let safe := fun draw : Tape (ParameterBounds.config profile) × TrialSeed profile =>
    safeResetAccept profile lanes root claims strategy (productionBad profile lanes root claims strategy) draw.1 draw.2
  have conditional : ∀ base, GoodPrefix safe base →
      1 - (1 / 4 : ℝ) ≤ probability (fun seed : Fin (knowledgeRounds profile gap) → TrialSeed profile =>
        extractionSuccess (extractor profile (knowledgeRounds profile gap))
          ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ (base, seed)) := by
    intro base good
    have large := production_good_prefix_heavy_mass profile lanes root claims strategy
      laneBound claimShape claimCap gap gapPositive advantage base good
    let certificate := Classical.choice (production_heavy_witness profile lanes root claims strategy base
      (heavyAvailability profile gap) (heavyAvailability_positive profile gap gapPositive) large)
    have recovered := conditional_extractor_schedule profile lanes root claims strategy laneBound
      (productionBad profile lanes root claims strategy) base (heavyAvailability profile gap)
      (heavyAvailability_positive profile gap gapPositive) (heavyAvailability_le_one profile gap gapLeOne)
      (availabilityBlock profile gap) 0 (availabilityBlock_enough profile gap gapPositive) large certificate
    change 1 - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ 0 ≤ _ at recovered
    convert recovered using 1 <;> simp only [knowledgeRounds, pow_zero, mul_one]
    unfold probability
    congr 1
  have chance := prefix_attempt_chance safe
    (extractionSuccess (extractor profile (knowledgeRounds profile gap))
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩)
    (1 / 4 : ℝ) (by norm_num) (by norm_num) conditional
  have mass := production_safe_mass profile lanes root claims strategy laneBound claimShape claimCap
  have budget : (knowledgeBadEnvelope : ℝ) ≤ (extractionCutoff : ℝ) := by
    norm_num [knowledgeBadEnvelope, extractionCutoff]
  dsimp only [safe] at chance
  nlinarith

/-- Acceptance PLUS failure for the actual repeated legal machine. Fuel uses
real inverse-gap blocks; the machine stops only on a verified explaining output. -/
theorem production_repeated_knowledge_failure (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (claimShape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN)
    (claimCap : claims.size ≤ 2 ^ 64) (gap : ℝ) (gapPositive : 0 < gap) (security : Nat)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)) :
    knowledgeFailureProbability
      (repeatedExtractor profile (knowledgeAttempts gap security) (knowledgeRounds profile gap))
      ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ ≤ (1 / 2 : ℚ) ^ security := by
  have chance := production_single_attempt_chance profile lanes root claims strategy laneBound
    claimShape claimCap gap gapPositive advantage
  have bound := repeatedExtractor_knowledge_failure profile (knowledgeAttempts gap security)
    (knowledgeRounds profile gap) lanes root claims strategy laneBound
    (gap / 4) (by positivity) chance
  have gapLeOne : gap / 4 ≤ 1 := by
    have acceptanceLeOne := le_one
      (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) strategy tape = true)
    have cutoffNonnegative : (0 : ℝ) ≤ (extractionCutoff : ℝ) := by norm_num [extractionCutoff]
    linarith
  have amplified := attempt_schedule_failure (gap / 4) (by positivity) gapLeOne
    (inverseGapBlock 4 gap) security (inverseGapBlock_enough 4 (by decide) gap gapPositive)
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [knowledgeAttempts, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    bound.trans amplified

#print axioms production_bad_probability
#print axioms production_safe_mass
#print axioms production_good_prefix_heavy_mass
#print axioms production_heavy_witness
#print axioms production_single_attempt_chance
#print axioms production_repeated_knowledge_failure
#check production_bad_probability
#check production_safe_mass
#check production_heavy_witness
#check production_single_attempt_chance
#check production_repeated_knowledge_failure
end Whir.PCSRewindExtractor
