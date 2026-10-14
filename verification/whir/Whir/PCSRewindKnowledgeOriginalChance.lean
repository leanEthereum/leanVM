import Whir.PCSRewindKnowledgeMass
import Whir.PCSRewindKnowledgeOriginalRecovery

/-! Fresh public prefixes are averaged pointwise. A rare accepting bad map is
charged, never assumed away or given the overall acceptance advantage. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame KnowledgeExtraction OriginalClaimsChecker
open PCSRewindExtractor SamplingProbability AuthenticatedResetProbability
open SupportedCandidateExtraction
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] ParameterBounds.config

theorem input_shapes {c : Config} {lanes m : Nat}
    {family : Fin m → RingPCSGame.FamilyClaim} {points : Array RingPCSGame.PointClaim}
    {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (r : RingPCSGame.Prefix)
    (j : Fin (OriginalClaimsChecker.input prepared root r).claims.size) :
    (OriginalClaimsChecker.input prepared root r).claims[j].weight.size = 2 ^ c.logN := by
  have old : ∀ claim ∈ (RingPCSGame.transformedClaims (2 ^ c.logN) family points r).toList,
      claim.weight.size = 2 ^ c.logN := by
    intro claim member
    obtain ⟨i, within, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    exact RingPCSGame.transformedClaims_shapes _ family points r ⟨i, within⟩
  have all : ∀ claim ∈ (OriginalClaimsChecker.input prepared root r).claims.toList,
      claim.weight.size = 2 ^ c.logN := by
    intro claim member
    rw [input_claims, Array.toList_push] at member
    rcases List.mem_append.mp member with member | member
    · exact old claim member
    · have eq : claim = (⟨CommitmentAnchor.weight c lanes anchorPoint, anchorValue⟩ : Claim) := by
        simpa using member
      simp [eq, CommitmentAnchor.weight, ArrayLayout.size_tab]
  exact all _ (by simp)

theorem input_size {c : Config} {lanes m : Nat}
    {family : Fin m → RingPCSGame.FamilyClaim} {points : Array RingPCSGame.PointClaim}
    {anchorPoint : Array E} {anchorValue : E}
    (prepared : Prepared c lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (r : RingPCSGame.Prefix) :
    (OriginalClaimsChecker.input prepared root r).claims.size = points.size + 2 := by
  rw [input_claims]
  simp [RingPCSGame.transformedClaims_size, Nat.add_comm, Nat.add_left_comm]

/-- Any actual returned word is separately covered by run_output_explains. -/
def attemptSuccess {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : Seed profile rounds) : Prop :=
  ∃ w, (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output = some w

open Classical in
/-- The probability bound is algebra on the actual product games, with no
per-prefix acceptance assumption hidden in its premise. -/
theorem average_attempt_mass {R A S : Type*} [Fintype R] [Nonempty R]
    [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]
    (accept : R × A → Prop) (success : R × S → Prop) (bad : R → Prop) (threshold : ℝ)
    (pointwise : ∀ r, (probability (fun a => accept (r, a)) - threshold -
      (if bad r then 1 else 0)) / 4 ≤ probability (fun s => success (r, s))) :
    (probability accept - threshold - probability bad) / 4 ≤ probability success := by
  classical
  have badAverage : probability bad = (∑ r, if bad r then (1 : ℝ) else 0) / Fintype.card R := by
    have single : ∀ r, probability (fun _ : Unit => bad r) = if bad r then (1 : ℝ) else 0 := by
      intro r
      by_cases h : bad r <;> simp [probability, h]
    have avg := probability_average (fun seed : R × Unit => bad seed.1)
    rw [product_left] at avg
    simpa only [single] using avg
  have sumBound := Finset.sum_le_sum (s := (Finset.univ : Finset R)) (fun r _ => pointwise r)
  have cardPositive : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [probability_average accept, probability_average success, badAverage]
  calc
    ((∑ r, probability (fun a => accept (r, a))) / Fintype.card R - threshold -
      (∑ r, if bad r then (1 : ℝ) else 0) / Fintype.card R) / 4 =
        (∑ r, (probability (fun a => accept (r, a)) - threshold -
          (if bad r then (1 : ℝ) else 0)) / 4) / Fintype.card R := by
      simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      field_simp [ne_of_gt cardPositive]
    _ ≤ (∑ r, probability (fun s => success (r, s))) / Fintype.card R :=
      div_le_div_of_nonneg_right sumBound cardPositive.le

theorem original_attempt_mass {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (claimCap : points.size + 2 ≤ 2 ^ 64) (gap : ℝ) (gapPositive : 0 < gap) :
    (probability (fun seed : RingPCSGame.Prefix × Tape (ParameterBounds.config profile) =>
       experiment (OriginalClaimsChecker.input prepared root seed.1) (strategy seed.1) seed.2 = true) -
      ((knowledgeBadEnvelope : ℝ) + 2 * (heavyQueryLoss profile : ℝ) + gap) -
      probability (RingPCSGame.Escape (ParameterBounds.config profile) lanes root family)) / 4 ≤
    probability (attemptSuccess profile (knowledgeRounds profile gap) lanes family points
      anchorPoint anchorValue prepared root strategy) := by
  classical
  apply average_attempt_mass
  intro r
  let claims := (OriginalClaimsChecker.input prepared root r).claims
  change (probability (fun tape : Tape (ParameterBounds.config profile) =>
    experiment (ExecutionShapes.Input profile lanes root claims) (strategy r) tape = true) -
    ((knowledgeBadEnvelope : ℝ) + 2 * (heavyQueryLoss profile : ℝ) + gap) -
    (if RingPCSGame.Escape (ParameterBounds.config profile) lanes root family r then 1 else 0)) / 4 ≤
    probability (fun seed : PCSRewindExtractor.Seed profile (knowledgeRounds profile gap) =>
      attemptSuccess profile (knowledgeRounds profile gap) lanes family points
        anchorPoint anchorValue prepared root strategy (r, seed))
  have actualCap : claims.size ≤ 2 ^ 64 := by
    dsimp only [claims]
    rw [input_size]
    exact claimCap
  have actualShapes : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config profile).logN :=
    input_shapes prepared root r
  have acceptedLeOne := le_one (fun tape : Tape (ParameterBounds.config profile) =>
    experiment (ExecutionShapes.Input profile lanes root claims) (strategy r) tape = true)
  have sourceNonnegative := nonneg (fun seed : PCSRewindExtractor.Seed profile (knowledgeRounds profile gap) =>
    attemptSuccess profile (knowledgeRounds profile gap) lanes family points
      anchorPoint anchorValue prepared root strategy (r, seed))
  have thresholdNonnegative : (0 : ℝ) ≤
      (knowledgeBadEnvelope : ℝ) + 2 * (heavyQueryLoss profile : ℝ) + gap := by
    have : (0 : ℝ) ≤ (heavyQueryLoss profile : ℝ) := by unfold heavyQueryLoss; positivity
    have : (0 : ℝ) ≤ (knowledgeBadEnvelope : ℝ) := by norm_num [knowledgeBadEnvelope]
    linarith
  by_cases escaped : RingPCSGame.Escape (ParameterBounds.config profile) lanes root family r
  · simp only [escaped, ite_true]
    linarith
  · simp only [escaped, ite_false, sub_zero]
    by_cases large : (knowledgeBadEnvelope : ℝ) + 2 * (heavyQueryLoss profile : ℝ) + gap <
        probability (fun tape : Tape (ParameterBounds.config profile) =>
          experiment (ExecutionShapes.Input profile lanes root claims) (strategy r) tape = true)
    · have generic := production_single_attempt_mass profile lanes root claims (strategy r)
        prepared.guards.2.2.2.1 actualShapes actualCap gap gapPositive large
      have dominates := mono
        (extractionSuccess (extractor profile (knowledgeRounds profile gap))
          ⟨ExecutionShapes.Input profile lanes root claims, strategy r⟩)
        (fun seed => attemptSuccess profile (knowledgeRounds profile gap) lanes family points
          anchorPoint anchorValue prepared root strategy (r, seed)) (by
            intro seed success
            obtain ⟨w, returned, _⟩ := success
            exact ⟨w, runOne_recovers_generic profile _ lanes family points anchorPoint anchorValue
              prepared root strategy (r, seed) escaped w returned⟩)
      have heavyNonnegative : (0 : ℝ) ≤ (heavyQueryLoss profile : ℝ) := by unfold heavyQueryLoss; positivity
      change (probability (fun tape => experiment (ExecutionShapes.Input profile lanes root claims) (strategy r) tape = true) -
        ((knowledgeBadEnvelope : ℝ) + 2 * (heavyQueryLoss profile : ℝ) + gap)) / 4 ≤ _
      linarith
    · linarith

/-- The extra public-map loss fits inside the already proved numerical margin;
the unchanged q56 cutoff is not rounded into a security level. -/
theorem original_amplified_cutoff (profile : ParameterBounds.Profile) (m : Nat) (cap : m ≤ 2 ^ 64) :
    (2 * heavyQueryLoss profile + knowledgeBadEnvelope + ringEscapeLoss m : ℚ) < extractionCutoff := by
  have margin := production_amplified_cutoff profile
  have ring := ringEscapeLoss_le m cap
  have small : (1 / (2 ^ 95 : ℚ)) < 1 / (2 ^ 55 : ℚ) := by norm_num
  linarith

theorem original_single_attempt_chance {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (familyCap : m ≤ 2 ^ 64) (claimCap : points.size + 2 ≤ 2 ^ 64)
    (gap : ℝ) (gapPositive : 0 < gap)
    (advantage : (extractionCutoff : ℝ) + gap ≤
      probability (fun seed : RingPCSGame.Prefix × Tape (ParameterBounds.config profile) =>
        experiment (OriginalClaimsChecker.input prepared root seed.1) (strategy seed.1) seed.2 = true)) :
    gap / 8 ≤ probability (attemptSuccess profile (knowledgeRounds profile (gap / 2)) lanes family points
      anchorPoint anchorValue prepared root strategy) := by
  have mass := original_attempt_mass profile lanes family points anchorPoint anchorValue prepared root strategy
    claimCap (gap / 2) (by positivity)
  have escape := ring_escape_probability profile lanes root family
  have margin : 2 * (heavyQueryLoss profile : ℝ) + knowledgeBadEnvelope + ringEscapeLoss m < extractionCutoff := by
    exact_mod_cast original_amplified_cutoff profile m familyCap
  linarith

#print axioms input_shapes
#print axioms input_size
#print axioms average_attempt_mass
#print axioms original_attempt_mass
#print axioms original_amplified_cutoff
#print axioms original_single_attempt_chance
#check original_single_attempt_chance
end Whir.PCSRewindSource
