import SphincsFors.H0Price
import SphincsFors.H0Numeric

/-! Ingredients of the H-term bounds: the fair share `wbarOf q` of the grinding signer and its
fair-share hypotheses, real forms of the landing probability and of Touchard sums, and the final
real inequality behind `(1 - budget 0 q) + q H_0(q) + (q + K + N) 2^-200 ≤ (q + K) / 2^127`. -/

open ENNReal

namespace SphincsFors.Security.H0

open Concrete Domination ForsPrice

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

variable [Params]

/-- Coin probability of the fair-share signer at budget `q` (with `Cmax = q + 2^32`). -/
noncomputable def wbarOf (q : ℕ) : ℝ≥0∞ := ((((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹

theorem subtree_le_26 : subtreeHeight ≤ 26 := (inferInstance : Params).subtreeHeight_le

theorem landing_eq : landing = ENNReal.ofReal (1 / 2 ^ (26 - subtreeHeight)) := by
  unfold landing
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_natCast]
  congr 1
  push_cast
  rfl

theorem card_eq : ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 ^ subtreeHeight) := by
  rw [Fintype.card_fin, ← ENNReal.ofReal_natCast]
  push_cast
  rfl

theorem dReal_pos (q : ℕ) (hq : q ≤ 2 ^ 127) : (0 : ℝ) < 2 ^ 128 - q - 2 ^ 32 := by
  have : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  linarith [show (2 : ℝ) ^ 128 = 2 * 2 ^ 127 by norm_num, show (2 : ℝ) ^ 32 < 2 ^ 127 by norm_num]

theorem wbar_eq (q : ℕ) (hq : q ≤ 2 ^ 127) :
    wbarOf q = ENNReal.ofReal (2 ^ (26 - subtreeHeight) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) := by
  have hq' : q + 2 ^ 32 ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hD : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((2 : ℝ) ^ 128 - q - 2 ^ 32) := by
    rw [← ENNReal.ofReal_natCast]
    congr 1
    rw [Nat.cast_sub hq']
    push_cast
    ring
  have hpos := dReal_pos q hq
  unfold wbarOf
  rw [hD, landing_eq, ← ENNReal.ofReal_mul hpos.le, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-! ### The fair-share hypotheses -/

theorem fair_of (q : ℕ) (hq : 2 * q ≤ 2 ^ 128) : ForsPotential.Fair (wbarOf q) (q + 2 ^ 32) := by
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hpos := dReal_pos q hq127
  have hw := wbar_eq q hq127
  have hcmax : q + 2 ^ 32 ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hland0 : landing ≠ 0 := by
    rw [landing_eq]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hlandT : landing ≠ ⊤ := by rw [landing_eq]; exact ENNReal.ofReal_ne_top
  have hD0 : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) ≠ 0 := by
    have : 0 < 2 ^ 128 - (q + 2 ^ 32) := by omega
    exact_mod_cast this.ne'
  have hDT : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hprod0 : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing ≠ 0 := mul_ne_zero hD0 hland0
  have hprodT : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing ≠ ⊤ := ENNReal.mul_ne_top hDT hlandT
  refine ⟨?_, ?_, hcmax, ?_⟩
  · unfold wbarOf; exact ENNReal.inv_ne_top.2 hprod0
  · rw [hw, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_one hpos]
    have h1 : (2 : ℝ) ^ (26 - subtreeHeight) ≤ 2 ^ 26 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq127
    have h3 : (2 : ℝ) ^ 26 + 2 ^ 32 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
    linarith
  · unfold wbarOf
    generalize (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) = Dn at hprod0 hprodT ⊢
    generalize ((2 ^ 128 : ℕ) : ℝ≥0∞) = T
    generalize landing = lam at hprod0 hprodT ⊢
    rw [div_eq_mul_inv]
    have : (Dn * lam)⁻¹ * (Dn * T⁻¹) * lam = ((Dn * lam)⁻¹ * (Dn * lam)) * T⁻¹ := by ring
    rw [this, ENNReal.inv_mul_cancel hprod0 hprodT, one_mul]

/-! ### Real forms of the ingredients -/

/-- Touchard sums commute with `ofReal`. -/
theorem touchard_ofReal (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    touchard n (ENNReal.ofReal r) =
      ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℝ) * r ^ j) := by
  unfold touchard
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr, ENNReal.ofReal_natCast]

theorem touchard_mono (n : ℕ) {μ μ' : ℝ≥0∞} (h : μ ≤ μ') : touchard n μ ≤ touchard n μ' := by
  unfold touchard
  gcongr

/-- The final real inequality. -/
theorem final_real (q qa qb Kc Nn Ar Le Y : ℝ) (hqa : qa ≤ q) (hqb : q ≤ qb) (hqa0 : 0 ≤ qa)
    (hAr : 0 ≤ Ar) (hLe0 : 0 ≤ Le) (hLe1 : Le < 1) (hY : Y ≤ Le / (1 - Le))
    (hcheck : qb * Ar * (Le / (1 - Le)) + (qb + Kc + Nn) / 2 ^ 200 ≤ (qa / 2 ^ 128) ^ 2 + Kc / 2 ^ 127) :
    (1 - ((2 ^ 128 - 0 - q) / (2 ^ 128 - 0)) ^ 2) + q * (Ar * Y) + (q + Kc + Nn) / 2 ^ 200 ≤
      (q + Kc) / 2 ^ 127 := by
  have hq0 : 0 ≤ q := le_trans hqa0 hqa
  have hF : 0 ≤ Le / (1 - Le) := div_nonneg hLe0 (by linarith)
  have h1 : q * (Ar * Y) ≤ qb * Ar * (Le / (1 - Le)) := by
    calc q * (Ar * Y) ≤ q * (Ar * (Le / (1 - Le))) := by gcongr
      _ ≤ qb * (Ar * (Le / (1 - Le))) := by gcongr
      _ = qb * Ar * (Le / (1 - Le)) := by ring
  have h2 : (qa / 2 ^ 128) ^ 2 ≤ (q / 2 ^ 128) ^ 2 := by gcongr
  have h3 : (q + Kc + Nn) / 2 ^ 200 ≤ (qb + Kc + Nn) / 2 ^ 200 := by gcongr
  have h4 : (1 - ((2 ^ 128 - 0 - q) / (2 ^ 128 - 0)) ^ 2) = 2 * q / 2 ^ 128 - (q / 2 ^ 128) ^ 2 := by
    simp only [sub_zero]
    field_simp
    ring
  have h5 : (q + Kc) / 2 ^ 127 = 2 * q / 2 ^ 128 + Kc / 2 ^ 127 := by
    field_simp
  rw [h4, h5]
  linarith

end SphincsFors.Security.H0
