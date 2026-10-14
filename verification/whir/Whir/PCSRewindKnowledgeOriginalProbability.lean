import Whir.RingPCSGame
import Whir.AnchorPrefixRefinementCaller
import Whir.PCSRewindKnowledgePrefix

/-! Original-family truth is not inferred from a compressed claim alone. This
bridge uses the actual fixed-root ring escape event and the SAME supported word
returned by the authenticated collector. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame
open SamplingProbability AuthenticatedResetProbability

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable def ringEscapeLoss (families : Nat) : ℚ :=
  (2 ^ 32 : ℚ) * (((families - 1 : Nat) : ℚ) / 2 ^ 192 + 1 / 2 ^ 160)

theorem ring_escape_probability {m : Nat} (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (family : Fin m → RingPCSGame.FamilyClaim) :
    probability (RingPCSGame.Escape (ParameterBounds.config p) lanes root family) ≤
      (ringEscapeLoss m : ℝ) := by
  classical
  rw [probability_eq_uniformProb]
  apply Rat.cast_le.mpr
  exact RingPCSGame.escape_probability p lanes root family

theorem ringEscapeLoss_le (m : Nat) (cap : m ≤ 2 ^ 64) :
    ringEscapeLoss m ≤ 1 / (2 ^ 95 : ℚ) := by
  have size : ((m - 1 : Nat) : ℚ) ≤ (2 ^ 64 : ℚ) := by
    exact_mod_cast (Nat.sub_le m 1).trans cap
  unfold ringEscapeLoss
  calc
    (2 ^ 32 : ℚ) * (((m - 1 : Nat) : ℚ) / 2 ^ 192 + 1 / 2 ^ 160) ≤
        (2 ^ 32 : ℚ) * ((2 ^ 64 : ℚ) / 2 ^ 192 + 1 / 2 ^ 160) := by
      gcongr
    _ ≤ 1 / (2 ^ 95 : ℚ) := by norm_num

/-- Outside the actual compression escape, all transformed claims imply all
original family slices, every ordinary/strided point, and the literal retained
anchor, for the SAME root-list word. -/
theorem original_truth_of_anchored_claims {m : Nat} (c : Config)
    (record : AnchoredHeaderCodec.Record) (root : BaseOracle)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (r : RingPCSGame.Prefix) (w : Witness c record.shape.lanes)
    (member : w ∈ InitialCandidates.witnesses c record.shape.lanes root)
    (outside : ¬ RingPCSGame.Escape c record.shape.lanes root family r)
    (pointShape : record.point.length = c.logN)
    (truth : ∀ claim ∈ (AnchorPrefixRefinement.anchoredClaims c record family points r).toList,
      dot (paddedWitness c record.shape.lanes w) claim.weight = claim.value) :
    RingPCSGame.Honest c record.shape.lanes family points w ∧
      CommitmentAnchor.value c record.shape.lanes w record.point.toArray = record.value := by
  classical
  have oldTruth : ∀ claim ∈ (RingPCSGame.transformedClaims (2 ^ c.logN) family points r).toList,
      dot (paddedWitness c record.shape.lanes w) claim.weight = claim.value := by
    intro claim old
    apply truth claim
    simp only [AnchorPrefixRefinement.anchoredClaims, Array.toList_push, List.mem_append]
    exact Or.inl old
  have compressed := oldTruth (RingPCSGame.familyPublic (2 ^ c.logN) family r)
    (by simp [RingPCSGame.transformedClaims])
  rw [RingPCSGame.dot_family] at compressed
  have slices : (fun j => (family j).slices) = RingPCSGame.honestSlices c record.shape.lanes family w := by
    by_contra different
    exact outside ⟨w, member, different, compressed.symm⟩
  refine ⟨⟨slices, ?_⟩, ?_⟩
  · intro point present
    apply oldTruth (RingPCSGame.publicPoint (2 ^ c.logN) point)
    simp only [RingPCSGame.transformedClaims, Array.toList_append, Array.toList_map,
      List.mem_append, List.mem_map]
    exact Or.inr ⟨point, present, rfl⟩
  · have anchor := truth
      (⟨CommitmentAnchor.weight c record.shape.lanes record.point.toArray, record.value⟩ : Claim)
      (by simp [AnchorPrefixRefinement.anchoredClaims])
    rw [CommitmentAnchor.weight_value c record.shape.lanes w record.point.toArray
      (by simpa using pointShape)] at anchor
    exact anchor

/-- The actual ring escape loss is unchanged when the adversary's complete
WHIR tape is included in the public-prefix experiment. -/
theorem joint_ring_escape_probability {m : Nat} (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (family : Fin m → RingPCSGame.FamilyClaim) :
    probability (fun seed : RingPCSGame.Prefix × Tape (ParameterBounds.config p) =>
      RingPCSGame.Escape (ParameterBounds.config p) lanes root family seed.1) ≤
        (ringEscapeLoss m : ℝ) := by
  classical
  rw [probability_eq_uniformProb]
  apply Rat.cast_le.mpr
  have bound := RingMapBatching.conditional_error
    (RingPCSGame.Escape (ParameterBounds.config p) lanes root family)
    (fun seed : RingPCSGame.Prefix × Tape (ParameterBounds.config p) =>
      RingPCSGame.Escape (ParameterBounds.config p) lanes root family seed.1)
    (ringEscapeLoss m) 0 (by norm_num)
    (RingPCSGame.escape_probability p lanes root family)
    (by
      intro r outside
      simp [outside, Soundness.uniformProb])
  simpa using bound

#print axioms ring_escape_probability
#print axioms ringEscapeLoss_le
#print axioms original_truth_of_anchored_claims
#print axioms joint_ring_escape_probability
end Whir.PCSRewindSource
