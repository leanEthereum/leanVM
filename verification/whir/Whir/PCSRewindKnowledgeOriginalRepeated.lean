import Whir.PCSRewindKnowledgeOriginalChance

/-! The repeated source machine stops only on an original-checked word. Its
failure probability is derived from actual independent seeds, not a supplied
availability event. The fuel is proof-chosen; the executable machine does not
compute the unknown prover acceptance probability. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame KnowledgeExtraction OriginalClaimsChecker
open PCSRewindExtractor SupportedCandidateExtraction SamplingProbability
open AuthenticatedResetProbability ResetAcceptanceAmplification

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] ParameterBounds.config

noncomputable instance sourceRepeatedSeedFintype (profile : ParameterBounds.Profile) (attempts rounds : Nat) :
    Fintype (RepeatedSeed profile attempts rounds) := by
  letI : Fintype (Seed profile rounds) := inferInstanceAs
    (Fintype (RingPCSGame.Prefix × PCSRewindExtractor.Seed profile rounds))
  exact inferInstanceAs (Fintype (Fin attempts → Seed profile rounds))

noncomputable def sourceRounds (profile : ParameterBounds.Profile) (gap : ℝ) : Nat :=
  knowledgeRounds profile (gap / 2)

noncomputable def sourceAttempts (gap : ℝ) (security : Nat) : Nat :=
  extractorAttempts (inverseGapBlock 8 gap) security

abbrev AcceptanceSeed (profile : ParameterBounds.Profile) :=
  RingPCSGame.Prefix × Tape (ParameterBounds.config profile)

/-- The actual source public preparation guard is part of the accepted event;
malformed dimensions are not granted generic dense-kernel acceptance. -/
def accepted {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : AcceptanceSeed profile) : Prop :=
  match prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue with
  | none => False
  | some prepared => experiment (OriginalClaimsChecker.input prepared root seed.1) (strategy seed.1) seed.2 = true

def failureEvent {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy)
    (draw : RepeatedSeed profile attempts rounds × AcceptanceSeed profile) : Prop :=
  accepted profile lanes family points anchorPoint anchorValue root strategy draw.2 ∧
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy draw.1).output = none

theorem attempts_failure_probability {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) :
    probability (fun seed : RepeatedSeed profile attempts rounds =>
      (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy (List.ofFn seed)).output = none) =
    (1 - probability (attemptSuccess profile rounds lanes family points anchorPoint anchorValue prepared root strategy)) ^ attempts := by
  classical
  have one : ∀ seed : Seed profile rounds,
      (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output = none ↔
      ¬ attemptSuccess profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed := by
    intro seed
    cases value : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output <;>
      simp [attemptSuccess, value]
  have events : (fun seed : RepeatedSeed profile attempts rounds =>
      (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy (List.ofFn seed)).output = none) =
      (fun seed => ∀ r, ¬ attemptSuccess profile rounds lanes family points anchorPoint anchorValue prepared root strategy (seed r)) := by
    funext seed
    apply propext
    rw [runAttempts_output_none_iff]
    constructor
    · intro all r
      exact (one (seed r)).mp (all _ (List.mem_ofFn.mpr ⟨r, rfl⟩))
    · intro all value member
      obtain ⟨r, rfl⟩ := List.mem_ofFn.mp member
      exact (one (seed r)).mpr (all r)
  rw [events]
  exact independent_misses _ attempts

theorem prepared_repeated_failure {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (familyCap : m ≤ 2 ^ 64) (claimCap : points.size + 2 ≤ 2 ^ 64)
    (gap : ℝ) (gapPositive : 0 < gap) (security : Nat)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (fun seed : AcceptanceSeed profile =>
        experiment (OriginalClaimsChecker.input prepared root seed.1) (strategy seed.1) seed.2 = true)) :
    probability (fun seed : RepeatedSeed profile (sourceAttempts gap security) (sourceRounds profile gap) =>
      (runAttempts profile (sourceRounds profile gap) lanes family points anchorPoint anchorValue prepared root strategy
        (List.ofFn seed)).output = none) ≤ (1 / 2 : ℝ) ^ security := by
  have chance : gap / 8 ≤ probability (attemptSuccess profile (sourceRounds profile gap) lanes family points
      anchorPoint anchorValue prepared root strategy) :=
    original_single_attempt_chance profile lanes family points anchorPoint anchorValue prepared root strategy
      familyCap claimCap gap gapPositive advantage
  have sourceLeOne := le_one (attemptSuccess profile (sourceRounds profile gap) lanes family points
    anchorPoint anchorValue prepared root strategy)
  have gapLeOne : gap / 8 ≤ 1 := chance.trans sourceLeOne
  rw [attempts_failure_probability]
  have amplified := attempt_schedule_failure (gap / 8) (by positivity) gapLeOne
    (inverseGapBlock 8 gap) security (inverseGapBlock_enough 8 (by decide) gap gapPositive)
  exact (pow_le_pow_left₀ (sub_nonneg.mpr sourceLeOne) (sub_le_sub_left chance 1) _).trans amplified

theorem repeated_knowledge_failure {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy)
    (familyCap : m ≤ 2 ^ 64) (claimCap : points.size + 2 ≤ 2 ^ 64)
    (gap : ℝ) (gapPositive : 0 < gap) (security : Nat)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (accepted profile lanes family points anchorPoint anchorValue root strategy)) :
    probability (failureEvent profile (sourceAttempts gap security) (sourceRounds profile gap) lanes family points
      anchorPoint anchorValue root strategy) ≤ (1 / 2 : ℝ) ^ security := by
  classical
  cases prepared : prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue with
  | none =>
    have noAcceptance : accepted profile lanes family points anchorPoint anchorValue root strategy = (fun _ => False) := by
      funext seed
      simp only [accepted, prepared]
    have noFailure : failureEvent profile (sourceAttempts gap security) (sourceRounds profile gap) lanes family points
        anchorPoint anchorValue root strategy = (fun _ => False) := by
      funext draw
      simp only [failureEvent, noAcceptance, false_and]
    rw [noFailure]
    have zero : probability (fun _ : RepeatedSeed profile (sourceAttempts gap security) (sourceRounds profile gap) ×
        AcceptanceSeed profile => False) = 0 := by simp [probability]
    rw [zero]
    positivity
  | some cached =>
    have acceptedEq : accepted profile lanes family points anchorPoint anchorValue root strategy =
        (fun seed : AcceptanceSeed profile =>
          experiment (OriginalClaimsChecker.input cached root seed.1) (strategy seed.1) seed.2 = true) := by
      funext seed
      simp only [accepted, prepared]
    rw [acceptedEq] at advantage
    have chance := prepared_repeated_failure profile lanes family points anchorPoint anchorValue cached root strategy
      familyCap claimCap gap gapPositive security advantage
    have dominated := mono (failureEvent profile (sourceAttempts gap security) (sourceRounds profile gap) lanes family points
      anchorPoint anchorValue root strategy)
      (fun draw => (runAttempts profile (sourceRounds profile gap) lanes family points anchorPoint anchorValue cached root strategy
        (List.ofFn draw.1)).output = none) (by
          intro draw failed
          simpa only [run, prepared] using failed.2)
    have projection : probability (fun draw : RepeatedSeed profile (sourceAttempts gap security)
        (sourceRounds profile gap) × AcceptanceSeed profile =>
        (runAttempts profile (sourceRounds profile gap) lanes family points anchorPoint anchorValue cached root strategy
          (List.ofFn draw.1)).output = none) =
        probability (fun seed : RepeatedSeed profile (sourceAttempts gap security) (sourceRounds profile gap) =>
          (runAttempts profile (sourceRounds profile gap) lanes family points anchorPoint anchorValue cached root strategy
            (List.ofFn seed)).output = none) :=
      product_left (A := RepeatedSeed profile (sourceAttempts gap security) (sourceRounds profile gap))
        (B := AcceptanceSeed profile)
        (fun seed => (runAttempts profile (sourceRounds profile gap) lanes family points anchorPoint anchorValue
          cached root strategy (List.ofFn seed)).output = none)
    exact dominated.trans (projection.le.trans chance)

theorem universal_knowledge_failure {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy)
    (familyCap : m ≤ 2 ^ 64) (claimCap : points.size + 2 ≤ 2 ^ 64) (security : Nat) :
    let κ := probability (accepted profile lanes family points anchorPoint anchorValue root strategy)
    let gap := κ - (extractionCutoff : ℝ)
    probability (failureEvent profile (sourceAttempts gap security) (sourceRounds profile gap) lanes family points
      anchorPoint anchorValue root strategy) ≤ (extractionCutoff : ℝ) + (1 / 2 : ℝ) ^ security := by
  classical
  dsimp only
  let κ := probability (accepted profile lanes family points anchorPoint anchorValue root strategy)
  by_cases high : (extractionCutoff : ℝ) < κ
  · have bound := repeated_knowledge_failure profile lanes family points anchorPoint anchorValue root strategy
      familyCap claimCap (κ - extractionCutoff) (by linarith) security (by dsimp only [κ]; linarith)
    have cutoffNonnegative : (0 : ℝ) ≤ (extractionCutoff : ℝ) := by norm_num [extractionCutoff]
    exact bound.trans (by linarith)
  · have dominated := mono
      (failureEvent profile (sourceAttempts (κ - extractionCutoff) security) (sourceRounds profile (κ - extractionCutoff))
        lanes family points anchorPoint anchorValue root strategy)
      (fun draw => accepted profile lanes family points anchorPoint anchorValue root strategy draw.2)
      (fun _ failed => failed.1)
    have projection : probability (fun draw : RepeatedSeed profile (sourceAttempts (κ - extractionCutoff) security)
        (sourceRounds profile (κ - extractionCutoff)) × AcceptanceSeed profile =>
        accepted profile lanes family points anchorPoint anchorValue root strategy draw.2) = κ := by
      have swap := probability_equiv (Equiv.prodComm _ _)
        (fun draw : AcceptanceSeed profile × RepeatedSeed profile (sourceAttempts (κ - extractionCutoff) security)
          (sourceRounds profile (κ - extractionCutoff)) =>
          accepted profile lanes family points anchorPoint anchorValue root strategy draw.1)
      exact swap.trans (product_left _)
    rw [projection] at dominated
    have noiseNonnegative : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ security := by positivity
    exact dominated.trans (by linarith)

 theorem sourceRounds_polynomial (profile : ParameterBounds.Profile) (gap : ℝ) (positive : 0 < gap) :
    (sourceRounds profile gap : ℝ) ≤
      ((8 * blockLength (ParameterBounds.config profile) : ℝ) / gap + 1) * ((initialDepth profile : ℝ) + 2) := by
  have bound := knowledgeRounds_polynomial profile (gap / 2) (by positivity)
  calc
    (sourceRounds profile gap : ℝ) ≤
        ((4 * blockLength (ParameterBounds.config profile) : ℝ) / (gap / 2) + 1) *
          ((initialDepth profile : ℝ) + 2) := bound
    _ = ((8 * blockLength (ParameterBounds.config profile) : ℝ) / gap + 1) *
          ((initialDepth profile : ℝ) + 2) := by
      field_simp [ne_of_gt positive]; ring

 theorem sourceAttempts_polynomial (gap : ℝ) (positive : 0 < gap) (security : Nat) :
    (sourceAttempts gap security : ℝ) ≤ ((8 : ℝ) / gap + 1) * security := by
  dsimp only [sourceAttempts, extractorAttempts]
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (inverseGapBlock_polynomial 8 gap positive) (Nat.cast_nonneg security)

#print axioms attempts_failure_probability
#print axioms prepared_repeated_failure
#print axioms repeated_knowledge_failure
#print axioms universal_knowledge_failure
#print axioms sourceRounds_polynomial
#print axioms sourceAttempts_polynomial
#check universal_knowledge_failure
end Whir.PCSRewindSource
