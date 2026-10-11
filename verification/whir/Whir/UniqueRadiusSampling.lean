import Whir.SamplingProbability
import Whir.ConcreteRowExtraction
import Whir.ParameterBounds

/-! Exact stratified query loss outside the unique-decoding radius. The target word is fixed before the query tape. This module proves a converse for the actual all-queries-agree event, not for arbitrary WHIR verifier acceptance. Connecting that event to the adaptive protocol trajectory is a separate obligation. -/
namespace Whir.UniqueRadiusSampling
open Concrete

/-- Agreement of one fixed received word with one fixed supported target. -/
def agreement (depth : Nat) (received target : Fin (2 ^ depth) → E) :
    Finset (Fin (2 ^ depth)) :=
  Finset.univ.filter fun i => received i = target i

theorem agreement_add_distance (depth : Nat) (received target : Fin (2 ^ depth) → E) :
    (agreement depth received target).card + hammingDist received target = 2 ^ depth := by
  classical
  simpa [agreement, hammingDist] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 ^ depth))))
      (fun i => received i = target i))

noncomputable def hitProbability (depth count : Nat)
    (received target : Fin (2 ^ depth) → E) : ℚ := by
  classical
  exact Soundness.uniformProb (Finset.univ.filter
    (SamplingProbability.allQueriesHit depth count (agreement depth received target)))

/-- The exact integer agreement cap outside Gao's radius, including the parity correction. -/
def queryLoss (depth dimension count : Nat) : ℚ :=
  (((((2 ^ depth + dimension - 1) / 2 : Nat) : ℚ) / (2 ^ depth : Nat)) ^ count)

/-- No iid replacement: the starting bound is the proved actual stratified sampler law. -/
theorem far_hitProbability_le (depth dimension count : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) (dimensionBound : dimension ≤ 2 ^ depth)
    (received target : Fin (2 ^ depth) → E)
    (far : 2 ^ depth - dimension < 2 * hammingDist received target) :
    hitProbability depth count received target ≤ queryLoss depth dimension count := by
  classical
  have partition := agreement_add_distance depth received target
  have cap : (agreement depth received target).card ≤ (2 ^ depth + dimension - 1) / 2 := by
    have sizePositive : 0 < 2 ^ depth := by positivity
    omega
  have sampled := SamplingProbability.actual_query_bound_rat depth count positive noWrap
    (agreement depth received target)
  calc
    hitProbability depth count received target ≤
        (((agreement depth received target).card : ℚ) / (2 ^ depth : Nat)) ^ count := sampled
    _ ≤ queryLoss depth dimension count := by
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_right (by exact_mod_cast cap) (by positivity)

/-- Nonnegligible agreement-event mass above the explicit loss forces the decoder radius for this fixed supported word. This is not an acceptance-to-radius theorem. -/
theorem hitProbability_above_implies_radius (depth dimension count : Nat)
    (positive : 0 < depth) (noWrap : depth ≤ 64) (dimensionBound : dimension ≤ 2 ^ depth)
    (received target : Fin (2 ^ depth) → E)
    (above : queryLoss depth dimension count < hitProbability depth count received target) :
    2 * hammingDist received target ≤ 2 ^ depth - dimension := by
  by_contra far
  exact (not_lt_of_ge (far_hitProbability_le depth dimension count positive noWrap dimensionBound
    received target (by omega))) above

/-- The actual rate-four production profile uses 56 initial stratified queries. -/
theorem rate_four_first_queries (size : Fin 14) :
    (ParameterBounds.config (size, (⟨3, by decide⟩ : Fin 4))).queries[0]! = 56 := by
  have all : ∀ size : Fin 14,
      (ParameterBounds.config (size, (⟨3, by decide⟩ : Fin 4))).queries[0]! = 56 := by
    decide +kernel
  exact all size

/-- Exact finite-size unique-radius sampling loss is no larger than the rate-four envelope. This is a fixed-target agreement event, not WHIR acceptance. -/
theorem rate_four_queryLoss_le (n : Nat) :
    queryLoss (n + 4) (2 ^ n) 56 ≤ (17 / 32 : ℚ) ^ 56 := by
  unfold queryLoss
  apply pow_le_pow_left₀ (by positivity)
  have size : 2 ^ (n + 4) = 16 * 2 ^ n := by
    rw [Nat.pow_add]
    norm_num
    omega
  have cap : 2 * ((2 ^ (n + 4) + 2 ^ n - 1) / 2) ≤ 17 * 2 ^ n := by
    have divided := Nat.mul_div_le (2 ^ (n + 4) + 2 ^ n - 1) 2
    omega
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 ^ (n + 4) : Nat))).mpr
  rw [size]
  have castCap : (2 : ℚ) * (((2 ^ (n + 4) + 2 ^ n - 1) / 2 : Nat) : ℚ) ≤
      17 * (2 ^ n : Nat) := by exact_mod_cast cap
  rw [size] at castCap
  push_cast at castCap ⊢
  linarith

/-- This envelope is between 2^-52 and 2^-51, and must not be advertised as a 128-bit bound. -/
theorem rate_four_envelope_bits :
    (1 / 2 ^ 52 : ℚ) < (17 / 32 : ℚ) ^ 56 ∧
      (17 / 32 : ℚ) ^ 56 < (1 / 2 ^ 51 : ℚ) := by
  norm_num

#print axioms agreement_add_distance
#print axioms far_hitProbability_le
#print axioms hitProbability_above_implies_radius
#print axioms rate_four_first_queries
#print axioms rate_four_queryLoss_le
#print axioms rate_four_envelope_bits

end Whir.UniqueRadiusSampling
