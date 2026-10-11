import Whir.MutualAgreement

/-! Analytic bounds for the exact BCHKS25 numerator. The hypotheses are rate,
length, agreement, and Johnson-gap facts, not an assumed security-bit bound. -/
namespace Whir.MutualAgreement

/-- The profile's relative Johnson gap bounds the exact list-theorem multiplicity.
The denominator is the full slack, not twice the slack. -/
theorem johnson_multiplicity_le_128 (rate alpha : ℝ) (halpha : 0 < alpha)
    (hgap : Real.sqrt rate ≤ (128 / 129 : ℝ) * alpha) :
    max ⌈Real.sqrt rate / (1 - Real.sqrt rate - (1 - alpha))⌉₊ 3 ≤ 128 := by
  have hslack : 0 < 1 - Real.sqrt rate - (1 - alpha) := by nlinarith
  apply max_le _ (by norm_num)
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hslack).mpr
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- A rate of at least 2^-26 gives a square-root rate of at least 2^-13. -/
theorem sqrt_rate_lower (rate : ℝ) (hlower : 1 / (2 : ℝ) ^ 26 ≤ rate) :
    1 / (2 : ℝ) ^ 13 ≤ Real.sqrt rate := by
  apply Real.le_sqrt_of_sq_le
  norm_num at hlower ⊢
  exact hlower

/-- A uniform analytic cap, derived solely from the production profile facts.
This does not assume the numerator bound or any claimed security-bit total. -/
theorem johnsonNumerator_le_two_pow_108 (N dimension : ℕ) (alpha : ℝ)
    (hrate_pos : 0 < ((dimension - 1 : ℕ) : ℝ) / N)
    (hrate_lower : 1 / (2 : ℝ) ^ 26 ≤ ((dimension - 1 : ℕ) : ℝ) / N)
    (hrate_upper : ((dimension - 1 : ℕ) : ℝ) / N ≤ 1)
    (hN : N ≤ 2 ^ 26) (halpha : 0 < alpha) (halpha_lt : alpha < 1)
    (hgap : Real.sqrt (((dimension - 1 : ℕ) : ℝ) / N) ≤
      (128 / 129 : ℝ) * alpha) :
    johnsonNumerator N dimension (1 - alpha) ≤ (2 : ℝ) ^ 108 := by
  let rate : ℝ := ((dimension - 1 : ℕ) : ℝ) / N
  let x := Real.sqrt rate
  let m : ℕ := max ⌈x / (1 - x - (1 - alpha))⌉₊ 3
  let t : ℝ := m + 1 / 2
  have hm : m ≤ 128 := johnson_multiplicity_le_128 rate alpha halpha hgap
  have ht_nonneg : 0 ≤ t := by dsimp [t]; positivity
  have ht_lt : t < 256 := by
    have hmR : (m : ℝ) ≤ 128 := by exact_mod_cast hm
    dsimp [t]
    linarith
  have ht : t ≤ 256 := ht_lt.le
  have hx : 1 / (2 : ℝ) ^ 13 ≤ x := sqrt_rate_lower rate hrate_lower
  have hx_pos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2 ^ 13).trans_le hx
  have hrate_nonneg : 0 ≤ rate := hrate_pos.le
  have hradius_nonneg : 0 ≤ 1 - alpha := by linarith
  have hradius_le : 1 - alpha ≤ 1 := by linarith
  have ht5 : t ^ 5 ≤ (256 : ℝ) ^ 5 := by gcongr
  have hsmall : 3 * t * (1 - alpha) * rate ≤ (3 : ℝ) * 256 * 1 * 1 := by
    gcongr
  have hnum : 2 * t ^ 5 + 3 * t * (1 - alpha) * rate ≤ (2 : ℝ) ^ 42 := by
    nlinarith [ht5, hsmall]
  have hcube : (1 / (2 : ℝ) ^ 13) ^ 3 ≤ x ^ 3 := by gcongr
  have hratio : (2 * t ^ 5 + 3 * t * (1 - alpha) * rate) / (3 * x ^ 3) ≤
      (2 : ℝ) ^ 81 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * x ^ 3)).mpr
    nlinarith [hcube]
  have hNR : (N : ℝ) ≤ (2 : ℝ) ^ 26 := by exact_mod_cast hN
  have hmain : ((2 * t ^ 5 + 3 * t * (1 - alpha) * rate) / (3 * x ^ 3)) * N ≤
      (2 : ℝ) ^ 107 := by
    calc
      _ ≤ (2 : ℝ) ^ 81 * (2 : ℝ) ^ 26 :=
        mul_le_mul hratio hNR (Nat.cast_nonneg _) (by positivity)
      _ = _ := by norm_num
  have htail : t / x ≤ (2 : ℝ) ^ 21 := by
    apply (div_le_iff₀ hx_pos).mpr
    nlinarith [hx]
  change ((2 * t ^ 5 + 3 * t * (1 - alpha) * rate) / (3 * x ^ 3)) * N + t / x ≤ _
  calc
    _ ≤ (2 : ℝ) ^ 107 + (2 : ℝ) ^ 21 := add_le_add hmain htail
    _ ≤ (2 : ℝ) ^ 108 := by norm_num

end Whir.MutualAgreement
