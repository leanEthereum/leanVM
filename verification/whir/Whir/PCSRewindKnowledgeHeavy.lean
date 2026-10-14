import Whir.SupportedCandidateRecovery
import Whir.PCSRewindKnowledgePrefix

/-! Exact heavy-support density arithmetic on all 56 source profiles. The
query envelope uses the MAXIMUM of Gao's integer half-distance cap and the
unchanged original commitment-list support threshold minus one. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability AuthenticatedResetSupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gaoAgreementCap (profile : ParameterBounds.Profile) : Nat :=
  (blockLength (ParameterBounds.config profile) + width (ParameterBounds.config profile) - 1) / 2

/-- Gao radius AND the unchanged original commitment-list threshold must both
hold. At rate one the conservative list threshold is slightly above Gao's
half-distance threshold, so Gao radius alone is not a certificate. -/
def heavyAgreementCap (profile : ParameterBounds.Profile) : Nat :=
  max (gaoAgreementCap profile) (ParameterBounds.threshold (ParameterBounds.config profile) 0 - 1)

def heavyQueryLoss (profile : ParameterBounds.Profile) : ℚ :=
  ((heavyAgreementCap profile : ℚ) / blockLength (ParameterBounds.config profile)) ^
    (ParameterBounds.config profile).queries[0]!

/-- Exact 56-profile bound uses actual varying query counts and both integer
thresholds; it never substitutes q=56 at rate one. -/
theorem production_heavyQueryLoss : ∀ profile : ParameterBounds.Profile,
    heavyQueryLoss profile ≤ radiusEnvelope := by
  decide +kernel

theorem production_heavy_static : ∀ p : ParameterBounds.Profile,
    0 < initialDepth p ∧ width (ParameterBounds.config p) < blockLength (ParameterBounds.config p) ∧
    ParameterBounds.threshold (ParameterBounds.config p) 0 ≤ heavyAgreementCap p + 1 := by
  decide +kernel

/-- Safe accepted mass above the exact query cap forces a common set large
enough for every live Gao lane AND the commitment-list certificate. -/
theorem production_heavy_size (profile : ParameterBounds.Profile)
    (accept : Trial (initialDepth profile) (ParameterBounds.config profile).queries[0]!
      (Suffix := E × Tape (ParameterBounds.config profile)) → Prop)
    (η : ℝ) (nonnegative : 0 ≤ η)
    (large : (heavyQueryLoss profile : ℝ) + blockLength (ParameterBounds.config profile) * η <
      probability accept) :
    let H := heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
      (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1 accept η
    2 * (blockLength (ParameterBounds.config profile) - H.card) ≤
        blockLength (ParameterBounds.config profile) - width (ParameterBounds.config profile) ∧
      ParameterBounds.threshold (ParameterBounds.config profile) 0 ≤ H.card := by
  dsimp only
  have envelope : (((heavyAgreementCap profile : ℝ) /
      blockLength (ParameterBounds.config profile)) ^ (ParameterBounds.config profile).queries[0]!) =
      (heavyQueryLoss profile : ℝ) := by
    simp [heavyQueryLoss, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  have above := heavy_card_gt (initialDepth profile) (ParameterBounds.config profile).queries[0]!
    (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
    accept η nonnegative (heavyAgreementCap profile) (by simpa only [envelope] using large)
  have dimensions := (production_heavy_static profile).2
  have gao : gaoAgreementCap profile <
      (heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
        (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1 accept η).card :=
    (Nat.le_max_left _ _).trans_lt above
  unfold gaoAgreementCap at gao
  constructor <;> omega

/-- Each available coordinate of a safe trial lies in its fixed agreement set.
This uses positive safe availability, not the fiction that all accepted
coordinates are true root rows. -/
theorem heavy_subset_of_safe_hits (depth count : Nat) (positive : 0 < depth) (noWrap : depth ≤ 64)
    {Suffix : Type*} [Fintype Suffix] [Nonempty Suffix]
    (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (ηpositive : 0 < η) (H : Finset (Fin (2 ^ depth)))
    (hits : ∀ trial, accept trial → ∀ i,
      RewindCoverage.sampledPosition depth count positive noWrap trial.1 i ∈ H) :
    heavy depth count positive noWrap accept η ⊆ H := by
  classical
  intro q member
  have available : η ≤ availability depth count positive noWrap accept q := by
    simpa only [heavy, Finset.mem_filter, Finset.mem_univ, true_and] using member
  by_contra outside
  have empty : (fun trial => accept trial ∧ Occurs depth count positive noWrap q trial) =
      (fun _ : Trial depth count (Suffix := Suffix) => False) := by
    funext trial
    apply propext
    constructor
    · rintro ⟨accepted, i, equal⟩
      exact outside (equal ▸ hits trial accepted i)
    · simp
  unfold availability at available
  rw [empty] at available
  simp [probability] at available
  linarith

/-- The analysis-safe subset is never tested by the executable collector.
Every accepted safe trial contributes its rows through the existing parser. -/
theorem safe_collector_covers (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (base : Tape (ParameterBounds.config profile))
    (safeAccept : TrialSeed profile → Prop)
    (safeAccepted : ∀ trial, safeAccept trial →
      experiment (ExecutionShapes.Input profile lanes root claims) strategy
        (fullResetTape (ExecutionShapes.Input profile lanes root claims) base
          (initialLevel profile) (initialDepth profile) (initialChunks profile) trial.1 trial.2) = true)
    (η : ℝ) (seed : Fin rounds → TrialSeed profile)
    (coverage : CoversHeavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
      (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1
      safeAccept η rounds seed) :
    let input := ExecutionShapes.Input profile lanes root claims
    let records := collectedRecords ⟨input, strategy⟩ (initialLevel profile) (initialDepth profile)
      (seedTapes profile rounds input rfl (base, seed))
    ∀ q ∈ heavy (initialDepth profile) (ParameterBounds.config profile).queries[0]!
        (production_heavy_static profile).1 (InitialCandidates.production_initial_facts profile).2.2.1 safeAccept η,
      ∃ record ∈ records, record.1 = q := by
  dsimp only
  intro q member
  obtain ⟨r, accepted, i, hit⟩ := coverage q member
  obtain ⟨record, recorded, coordinate⟩ := trialRecords_contains
    ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩
    (fullResetTape (ExecutionShapes.Input profile lanes root claims) base
      (initialLevel profile) (initialDepth profile) (initialChunks profile) (seed r).1 (seed r).2)
    (initialLevel profile) (initialDepth profile) (production_heavy_static profile).1
    (InitialCandidates.production_initial_facts profile).2.2.1 (seed r).1
    (fullResetTape_squeezes _ _ _ _ _ _ _) (safeAccepted (seed r) accepted) i
  refine ⟨record, List.mem_flatMap.mpr ⟨_, ?_, recorded⟩, coordinate.trans hit⟩
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

/-- Literal base projection cannot discard an authenticated Root0 record. -/
theorem baseRecords_covers {N : Nat} (root : BaseOracle) (records : List (Fin N × Array E))
    (authenticated : ∀ record ∈ records, record.2 = (root[record.1.val]!).map E.ofK)
    (q : Fin N) (covered : ∃ record ∈ records, record.1 = q) :
    ∃ record ∈ baseRecords records, record.1 = q := by
  obtain ⟨record, recorded, coordinate⟩ := covered
  refine ⟨(record.1, root[record.1.val]!), List.mem_filterMap.mpr ⟨record, recorded, ?_⟩, coordinate⟩
  rw [authenticated record recorded, baseRow_embedded]
  rfl

#print axioms production_heavy_size
#print axioms heavy_subset_of_safe_hits
end Whir.PCSRewindExtractor
