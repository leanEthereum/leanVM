import Whir.PCSRewindKnowledgeHeavy

/-! The extraction cutoff is evaluated AFTER safe-prefix κ/2 averaging and
unioning the actual protocol analysis losses. It is not a 128-bit claim. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open SamplingProbability AuthenticatedResetProbability AuthenticatedResetSupport

/-- The production event ledger proves this conservative whole-tape bound. -/
def knowledgeBadEnvelope : ℚ := 1 / 2 ^ 72

/-- All 56 source profiles retain a positive gap after the factor TWO from
prefix averaging, and after the complete bad-event envelope. -/
theorem production_amplified_cutoff (profile : ParameterBounds.Profile) :
    (1 / 2 ^ 55 : ℚ) < extractionCutoff -
      (2 * heavyQueryLoss profile + knowledgeBadEnvelope) := by
  have envelope := production_heavyQueryLoss profile
  have gap : (1 / 2 ^ 55 : ℚ) < extractionCutoff -
      (2 * radiusEnvelope + knowledgeBadEnvelope) := by
    norm_num [extractionCutoff, radiusEnvelope, knowledgeBadEnvelope]
  linarith

/-- Real collector fuel is inverse-gap blocks times the coordinate/security
logarithms. These counts parameterize the executable machine itself. -/
def collectorRounds (inverseAvailability coordinateLog security : Nat) : Nat :=
  inverseAvailability * (coordinateLog + 2 + security)

def extractorAttempts (inverseChance security : Nat) : Nat := inverseChance * security

/-- No logarithmic or field-size enumeration is hidden in the fuel schedule. -/
theorem collector_schedule_failure (depth count : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) {Suffix : Type*} [Fintype Suffix] [Nonempty Suffix]
    (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (ηpositive : 0 < η) (ηle : η ≤ 1)
    (block security : Nat) (enough : 1 ≤ (block : ℝ) * η) :
    probability (fun seed => ¬ CoversHeavy depth count positive noWrap accept η
      (collectorRounds block depth security) seed) ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ security := by
  have bound := polynomial_availability_schedule depth count positive noWrap accept
    η ηpositive ηle block (depth + 2 + security) enough
  have identity : ((2 ^ depth : Nat) : ℝ) * (1 / 2 : ℝ) ^ (depth + 2 + security) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ security := by
    rw [pow_add, pow_add]
    push_cast
    calc
      _ = ((2 : ℝ)^depth * (1/2 : ℝ)^depth) * (1/2 : ℝ)^2 * (1/2 : ℝ)^security := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  exact bound.trans_eq identity

/-- Independent verified attempts use inverse-chance blocks, not an observer
that terminates on the first accepted prefix. -/
theorem attempt_schedule_failure (chance : ℝ) (positive : 0 < chance) (leOne : chance ≤ 1)
    (block security : Nat) (enough : 1 ≤ (block : ℝ) * chance) :
    (1 - chance) ^ (extractorAttempts block security) ≤ (1 / 2 : ℝ) ^ security := by
  rw [extractorAttempts, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr leOne) block)
    (inverse_availability_block chance positive leOne block enough) security

/-- The actual natural inverse-availability block. -/
noncomputable def inverseGapBlock (scale : Nat) (gap : ℝ) : Nat :=
  Nat.ceil ((scale : ℝ) / gap)

theorem inverseGapBlock_enough (scale : Nat) (scalePositive : 0 < scale)
    (gap : ℝ) (gapPositive : 0 < gap) :
    1 ≤ (inverseGapBlock scale gap : ℝ) * (gap / scale) := by
  have scaleReal : (0 : ℝ) < scale := by exact_mod_cast scalePositive
  have bound := Nat.le_ceil ((scale : ℝ) / gap)
  have multiply := mul_le_mul_of_nonneg_right bound (div_nonneg gapPositive.le scaleReal.le)
  have reciprocal : ((scale : ℝ) / gap) * (gap / scale) = 1 := by
    field_simp [ne_of_gt gapPositive, ne_of_gt scaleReal]
  simpa only [inverseGapBlock, reciprocal] using multiply

/-- Ceil introduces at most one extra inverse-gap unit, so the real fuel is
polynomial in N, inverse acceptance gap, and coordinate/security logarithms. -/
theorem inverseGapBlock_polynomial (scale : Nat) (gap : ℝ) (gapPositive : 0 < gap) :
    (inverseGapBlock scale gap : ℝ) ≤ (scale : ℝ) / gap + 1 :=
  (Nat.ceil_lt_add_one (div_nonneg (by positivity) gapPositive.le)).le

/-- Availability and attempt schedules are parameters of the REAL extractor.
The acceptance gap is an explicit caller-supplied positive lower bound. Its
derivation from the actual causal acceptance mass is proved in production. -/
noncomputable def heavyAvailability (profile : ParameterBounds.Profile) (gap : ℝ) : ℝ :=
  gap / (4 * blockLength (ParameterBounds.config profile) : Nat)

noncomputable def availabilityBlock (profile : ParameterBounds.Profile) (gap : ℝ) : Nat :=
  inverseGapBlock (4 * blockLength (ParameterBounds.config profile)) gap

noncomputable def knowledgeRounds (profile : ParameterBounds.Profile) (gap : ℝ) : Nat :=
  collectorRounds (availabilityBlock profile gap) (initialDepth profile) 0

noncomputable def knowledgeAttempts (gap : ℝ) (security : Nat) : Nat :=
  extractorAttempts (inverseGapBlock 4 gap) security

theorem heavyAvailability_positive (profile : ParameterBounds.Profile) (gap : ℝ)
    (positive : 0 < gap) : 0 < heavyAvailability profile gap := by
  unfold heavyAvailability
  exact div_pos positive (by positivity)

theorem heavyAvailability_le_one (profile : ParameterBounds.Profile) (gap : ℝ)
    (leOne : gap ≤ 1) : heavyAvailability profile gap ≤ 1 := by
  unfold heavyAvailability
  apply (div_le_one (by positivity)).mpr
  have Npositive : (1 : Nat) ≤ blockLength (ParameterBounds.config profile) := by
    exact Nat.succ_le_of_lt (by unfold blockLength; positivity)
  have scale : (1 : ℝ) ≤ (4 * blockLength (ParameterBounds.config profile) : Nat) := by
    exact_mod_cast (by omega : (1 : Nat) ≤ 4 * blockLength (ParameterBounds.config profile))
  exact leOne.trans scale

theorem availabilityBlock_enough (profile : ParameterBounds.Profile) (gap : ℝ) (positive : 0 < gap) :
    1 ≤ (availabilityBlock profile gap : ℝ) * heavyAvailability profile gap :=
  inverseGapBlock_enough _ (by unfold blockLength; positivity) gap positive

/-- Literal collector fuel is polynomial in the domain size and inverse
acceptance gap, including the bit-depth needed for complete coverage. -/
theorem knowledgeRounds_polynomial (profile : ParameterBounds.Profile) (gap : ℝ) (positive : 0 < gap) :
    (knowledgeRounds profile gap : ℝ) ≤
      ((4 * blockLength (ParameterBounds.config profile) : ℝ) / gap + 1) *
        ((initialDepth profile : ℝ) + 2) := by
  have bound := inverseGapBlock_polynomial (4 * blockLength (ParameterBounds.config profile)) gap positive
  dsimp only [knowledgeRounds, collectorRounds, availabilityBlock, Nat.add_zero]
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_right bound (by positivity : (0 : ℝ) ≤ (initialDepth profile : ℝ) + 2)

/-- The actual independent-attempt fuel is linear in the desired failure
exponent and polynomial in the inverse acceptance gap. -/
theorem knowledgeAttempts_polynomial (gap : ℝ) (positive : 0 < gap) (security : Nat) :
    (knowledgeAttempts gap security : ℝ) ≤ ((4 : ℝ) / gap + 1) * security := by
  dsimp only [knowledgeAttempts, extractorAttempts]
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (inverseGapBlock_polynomial 4 gap positive) (Nat.cast_nonneg security)

#print axioms production_amplified_cutoff
#print axioms collector_schedule_failure
#print axioms attempt_schedule_failure
#print axioms knowledgeRounds_polynomial
#print axioms knowledgeAttempts_polynomial
end Whir.PCSRewindExtractor
