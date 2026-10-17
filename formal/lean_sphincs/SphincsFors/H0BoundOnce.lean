import SphincsFors.H0Bound
import SphincsFors.H0Once

/-! The one-coin Poisson rate at budget `q`, the rate of the signatures plus one coin per future
pair (no inflation of the signature loads by the cached share), is below the rational bound
`muOnceQ` at the right end of a budget interval. -/

open ENNReal

namespace SphincsFors.Security.H0

open Concrete Domination ForsPrice

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

/-! ### The rational rate bound -/

/-- Upper bound for the one-coin Poisson rate at the right end `qb` of an interval. -/
def muOnceQ (b N qb R : ℕ) : ℚ :=
  (N : ℚ) / 2 ^ b +
    ((qb : ℚ) / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) * (1 + 2 ^ 26 / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) ^ (24 * R) / 2 ^ b

variable [Params]

/-- The one-coin Poisson rate, in real form, is below the certificate bound. -/
theorem mu_leO (b N R q qb : ℕ) (hb : subtreeHeight = b) (hq : q ≤ qb) (hqb : 2 * qb ≤ 2 ^ 128) (μh : ℝ)
    (hμ : (muOnceQ b N qb R : ℝ) ≤ μh) :
    (N : ℝ≥0∞) * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)⁻¹ +
      (q : ℝ≥0∞) * (landing * wbarOf q *
        (1 + wbarOf q * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ^ (24 * R) /
          ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal μh := by
  have hqb127 : qb ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hq127 : q ≤ 2 ^ 127 := le_trans hq hqb127
  have hDq := dReal_pos q hq127
  have hDb := dReal_pos qb hqb127
  rw [wbar_eq q hq127, landing_eq, card_eq, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast q,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  simp (disch := positivity) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_div_of_pos]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hμ
  rw [hb]
  have hb26 : b ≤ 26 := hb ▸ subtree_le_26
  have hM : (2 : ℝ) ^ (26 - b) * 2 ^ b = 2 ^ 26 := by rw [← pow_add, Nat.sub_add_cancel hb26]
  have hML : (2 : ℝ) ^ (26 - b) / ((2 : ℝ) ^ 128 - q - 2 ^ 32) * 2 ^ b = 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32) := by
    rw [div_mul_eq_mul_div, hM]
  rw [hML]
  have hform : (N : ℝ) * (2 ^ b)⁻¹ +
      q * (1 / 2 ^ (26 - b) * (2 ^ (26 - b) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) *
        (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) / 2 ^ b) =
      (N : ℝ) / 2 ^ b + ((q : ℝ) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) *
        (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) / 2 ^ b := by
    field_simp
  rw [hform]
  unfold muOnceQ
  push_cast
  have hqq : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have hDle : (2 : ℝ) ^ 128 - qb - 2 ^ 32 ≤ 2 ^ 128 - q - 2 ^ 32 := by linarith
  have h1 : (2 : ℝ) ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32) ≤ 2 ^ 26 / ((2 : ℝ) ^ 128 - qb - 2 ^ 32) :=
    div_le_div_of_nonneg_left (by positivity) hDb hDle
  have h2 : (q : ℝ) / ((2 : ℝ) ^ 128 - q - 2 ^ 32) ≤ (qb : ℝ) / ((2 : ℝ) ^ 128 - qb - 2 ^ 32) := by
    rw [div_le_div_iff₀ hDq hDb]
    nlinarith
  gcongr

end SphincsFors.Security.H0
