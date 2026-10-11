import Whir.RewindBatchTarget
import Whir.UniqueRadiusSampling
import Whir.RewindCoverage

/-! Actual accepted query resets hit a fixed Root1/OOD-selected target outside the explicitly charged causal and batched-polynomial collision events. The target is fixed before query squeezes/lambda. This is the projection step toward extraction, not an assumption that acceptance puts every initial base lane in the unique radius. -/
namespace Whir.RewindRadiusExtraction
open Concrete Protocol CausalGame CausalExecution ExecutionShapes ParameterBounds VerifierInvariant
open CausalProbability LevelBoundary QueryBatchSoundness RewindBatchTarget Classical
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem accepted_reset_fixed_target (profile : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (tape : Tape (config profile))
    (level : Fin (config profile).folds.size)
    (hasNext : level.val + 1 < (config profile).folds.size) (draw : Sample (.query level))
    (target : Array E)
    (matching : Target (followingCandidates (Input profile lanes root claims) strategy tape level)
      (challenges (config profile) tape).levels[level.val]!.oodPoints[0]!
      (proof (Input profile lanes root claims) strategy tape).levels[level.val]!.oods[0]!.value target)
    (separated : Separated (followingCandidates (Input profile lanes root claims) strategy tape level)
      (challenges (config profile) tape).levels[level.val]!.oodPoints[0]!)
    (accepted : experiment (Input profile lanes root claims) strategy (set (.query level) tape draw) = true)
    (safe : ∀ q, ¬ CausalBadEvents.Bad (Input profile lanes root claims) strategy q
      (set (.query level) tape draw))
    (outside : ¬ Collision (remaining (config profile) level) (config profile).rates[level.val]!
      (config profile).queries[level.val]! level
      (levelAt (Input profile lanes root claims) strategy tape level).oracle
      (challenges (config profile) tape).levels[level.val]!
      (proof (Input profile lanes root claims) strategy tape).levels[level.val]!
      (CausalBoundary.boundary (Input profile lanes root claims) strategy tape level).state
      (followingCandidates (Input profile lanes root claims) strategy tape level) draw.1 draw.2) :
    SamplingProbability.allQueriesHit
      (remaining (config profile) level + (config profile).rates[level.val]!)
      (config profile).queries[level.val]!
      (agreeingColumns (remaining (config profile) level) (config profile).rates[level.val]! target
        (oldWord (remaining (config profile) level) (config profile).rates[level.val]!
          (levelAt (Input profile lanes root claims) strategy tape level).oracle
          (level.val == 0) (challenges (config profile) tape).levels[level.val]!.folds)) draw.1 := by
  let input := Input profile lanes root claims
  have restored := accepted_reset_restores profile lanes root claims strategy tape level hasNext draw
    accepted safe
  have facts := CausalBoundary.production_boundary_facts profile level
  have sizes := CausalBoundary.followingCandidates_sizes input strategy tape profile rfl level
    (by intro impossible; exact (impossible hasNext).elim)
  have weight : (CausalBoundary.boundary input strategy tape level).state.weight.size =
      2 ^ remaining (config profile) level := by
    have shape := (foldAt_shape profile lanes root claims strategy tape level
      (config profile).folds[level.val]! le_rfl).2
    simpa only [CausalBoundary.boundary, input, Nat.sub_self, Nat.add_zero] using shape
  have oods : ∀ j < (proof input strategy tape).levels[level.val]!.oods.size,
      (eqTable (challenges (config profile) tape).levels[level.val]!.oodPoints[j]!).size =
        2 ^ remaining (config profile) level := by
    intro j bound
    rw [CausalBoundary.decoded_oods_size] at bound
    exact CausalBoundary.point_size input tape level j bound
  have first : 0 < (proof input strategy tape).levels[level.val]!.oods.size := by
    rw [CausalBoundary.decoded_oods_size]
    exact (facts.2.2 hasNext).2
  exact restores_fixed_target _ _ _ _ _ _ _ _ _ _ _ sizes weight oods facts.1 facts.2.1
    first target matching separated draw restored outside

/-- The adjacent fresh lambda does not change the fixed-target hit probability. This is a product-coordinate identity, not a Fiat Shamir independence assertion. -/
theorem lifted_hit_probability (depth count : Nat)
    (received target : Fin (2 ^ depth) → E) :
    Soundness.uniformProb (Finset.univ.filter
      (fun draw : RewindCoverage.QueryTape depth count × E =>
        SamplingProbability.allQueriesHit depth count
          (UniqueRadiusSampling.agreement depth received target) draw.1)) =
      UniqueRadiusSampling.hitProbability depth count received target := by
  unfold UniqueRadiusSampling.hitProbability Soundness.uniformProb
  rw [← Finset.univ_product_univ]
  rw [Finset.filter_product_left
    (s := (Finset.univ : Finset (RewindCoverage.QueryTape depth count)))
    (t := (Finset.univ : Finset E))
    (SamplingProbability.allQueriesHit depth count
      (UniqueRadiusSampling.agreement depth received target))]
  rw [Finset.card_product, Fintype.card_prod, Finset.card_univ]
  push_cast
  have domainPositive : (Fintype.card (RewindCoverage.QueryTape depth count) : ℚ) ≠ 0 := by
    positivity
  have fieldPositive : (Fintype.card E : ℚ) ≠ 0 := by positivity
  field_simp [domainPositive, fieldPositive]

/-- A pointwise, already-derived actual-hit cover converts conditional accepted mass to the exact strict unique-decoding radius. It applies to the accepted-reset event proved above, not to unrestricted acceptance. -/
theorem hit_cover_above_implies_radius (depth dimension count : Nat)
    (positive : 0 < depth) (noWrap : depth ≤ 64) (dimensionBound : dimension ≤ 2 ^ depth)
    (received target : Fin (2 ^ depth) → E)
    (event : RewindCoverage.QueryTape depth count × E → Prop)
    (cover : ∀ draw, event draw → SamplingProbability.allQueriesHit depth count
      (UniqueRadiusSampling.agreement depth received target) draw.1)
    (above : UniqueRadiusSampling.queryLoss depth dimension count <
      Soundness.uniformProb (Finset.univ.filter event)) :
    2 * hammingDist received target ≤ 2 ^ depth - dimension := by
  have subset : (Finset.univ.filter event) ⊆
      Finset.univ.filter (fun draw : RewindCoverage.QueryTape depth count × E =>
        SamplingProbability.allQueriesHit depth count
          (UniqueRadiusSampling.agreement depth received target) draw.1) := by
    intro draw member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cover draw (Finset.mem_filter.mp member).2⟩
  have mass : Soundness.uniformProb (Finset.univ.filter event) ≤
      UniqueRadiusSampling.hitProbability depth count received target := by
    rw [← lifted_hit_probability]
    unfold Soundness.uniformProb
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Finset.card_le_card subset
    · positivity
  exact UniqueRadiusSampling.hitProbability_above_implies_radius depth dimension count
    positive noWrap dimensionBound received target (above.trans_le mass)

#print axioms lifted_hit_probability
#print axioms hit_cover_above_implies_radius

#print axioms accepted_reset_fixed_target
end Whir.RewindRadiusExtraction
