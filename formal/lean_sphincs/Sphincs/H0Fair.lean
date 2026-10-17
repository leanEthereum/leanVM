import Sphincs.BridgeForsPotentialOnce
import SphincsFors.H0Assembly
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The fair share `wbarOf q` of the grinding signer at budget `q`, its fair-share hypotheses, real
forms of the landing probability, and the final real inequality behind
`(1 - budget 0 q) + q H(q) + (q + K + N) 2^-200 ≤ (q + K) / 2^127`. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete ForestPrice ForsPotential

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

variable [Params]

/-- The inverse of the landing probability. -/
def scanM : ℕ := 2 ^ (26 - subtreeHeight)

/-- The cap on the cached landed pairs of unsigned messages at budget `q`: `65 ⌈q / (64 M)⌉ + 2^15`. -/
def LmaxOf (q : ℕ) : ℕ := 65 * ((q + 64 * scanM - 1) / (64 * scanM)) + 2 ^ 15

/-- The mass that the group of a message keeps on the identity, times `2^128`, at budget `q`. -/
def denOf (q : ℕ) : ℕ := 2 ^ 128 - (q + 2 ^ 32 + (scanM - 1) * LmaxOf q)

/-- Coin probability of the scan signer at budget `q` (with `Cmax = q + 2^32`, `Lmax = LmaxOf q`):
`(2 M − 1) / denOf q`, so that `landing · wbarOf q = (2 − landing) / denOf q`. -/
noncomputable def wbarOf (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * (scanM : ℝ) - 1) / (denOf q : ℝ))

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

theorem scanM_pos : 0 < scanM := Nat.two_pow_pos _

theorem landing_eq_M : landing = ENNReal.ofReal (1 / (scanM : ℝ)) := by
  rw [landing_eq]
  congr 2
  unfold scanM
  push_cast
  rfl

/-! ### The fair-rate hypotheses -/

/-- **The coin of the scan signer is fair** at every budget whose identity mass pays it. -/
theorem fair_of (q : ℕ) (hq : q + 2 ^ 32 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128) :
    FairS (wbarOf q) (q + 2 ^ 32) (LmaxOf q) := by
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  have hD : denOf q + (q + 2 ^ 32 + (scanM - 1) * LmaxOf q) = 2 ^ 128 := by unfold denOf; omega
  have hDge : 2 * scanM - 1 ≤ denOf q := by unfold denOf; omega
  have hDpos : (0 : ℝ) < (denOf q : ℝ) := by
    have : 0 < denOf q := by have := scanM_pos; omega
    exact_mod_cast this
  have hDr : (denOf q : ℝ) = 2 ^ 128 - ((q : ℝ) + 2 ^ 32 + ((scanM : ℝ) - 1) * (LmaxOf q : ℝ)) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hD
    push_cast [Nat.cast_sub scanM_pos] at h
    linarith
  have hDger : 2 * (scanM : ℝ) - 1 ≤ (denOf q : ℝ) := by
    have h : ((2 * scanM - 1 : ℕ) : ℝ) ≤ (denOf q : ℝ) := by exact_mod_cast hDge
    have h2 : ((2 * scanM - 1 : ℕ) : ℝ) = 2 * (scanM : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := scanM_pos; omega)]; push_cast; ring
    linarith
  refine ⟨?_, ?_⟩
  · unfold wbarOf
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one hDpos).2 hDger)
  · have hc : (Fintype.card Randomness : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
      rw [GraphView.card_randomness, one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 1
      rw [← ENNReal.ofReal_natCast]
      congr 1
      norm_num
    have hl1 : (1 : ℝ≥0∞) - landing = ENNReal.ofReal (1 - 1 / (scanM : ℝ)) := by
      rw [landing_eq_M, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
    have h1M : (0 : ℝ) ≤ 1 - 1 / (scanM : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hM
    rw [hc, hl1, landing_eq_M, hnat (q + 2 ^ 32), hnat (LmaxOf q)]
    unfold wbarOf
    have hsub : (0 : ℝ) ≤ 1 / (scanM : ℝ) * (((q + 2 ^ 32 : ℕ) : ℝ) * (1 / 2 ^ 128)) +
        (LmaxOf q : ℝ) * (1 - 1 / (scanM : ℝ)) * (1 / 2 ^ 128) := by positivity
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add h1M (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_sub _ hsub, ← ENNReal.ofReal_mul (by
        apply div_nonneg _ hDpos.le; linarith)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hM0 : (scanM : ℝ) ≠ 0 := by linarith
    push_cast
    rw [hDr] at hDpos ⊢
    field_simp
    ring

theorem wbar_le_one (q : ℕ) (hq : q + 2 ^ 32 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128) :
    wbarOf q ≤ 1 := (fair_of q hq).le_one

/-- The creation rate of the scan signer: `landing · wbarOf q = (2 − landing) / denOf q`. -/
theorem landing_mul_wbar (q : ℕ) (hq : q + 2 ^ 32 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128) :
    (landing * wbarOf q).toReal = (2 - 1 / (scanM : ℝ)) / (denOf q : ℝ) := by
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  have hDpos : (0 : ℝ) < (denOf q : ℝ) := by
    have : 0 < denOf q := by unfold denOf; have := scanM_pos; omega
    exact_mod_cast this
  unfold wbarOf
  rw [landing_eq_M, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by
    apply mul_nonneg (by positivity); apply div_nonneg _ hDpos.le; linarith)]
  have hM0 : (scanM : ℝ) ≠ 0 := by linarith
  field_simp

/-! ### Monotonicity in the budget -/

theorem LmaxOf_mono {q q' : ℕ} (h : q ≤ q') : LmaxOf q ≤ LmaxOf q' := by
  unfold LmaxOf
  have : (q + 64 * scanM - 1) / (64 * scanM) ≤ (q' + 64 * scanM - 1) / (64 * scanM) :=
    Nat.div_le_div_right (by omega)
  omega

/-- The fair-rate condition of a budget holds at every smaller budget. -/
theorem fair_cond_mono {q q' : ℕ} (h : q ≤ q')
    (hq' : q' + 2 ^ 32 + (scanM - 1) * LmaxOf q' + (2 * scanM - 1) ≤ 2 ^ 128) :
    q + 2 ^ 32 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128 := by
  have := Nat.mul_le_mul_left (scanM - 1) (LmaxOf_mono h)
  omega

theorem denOf_anti {q q' : ℕ} (h : q ≤ q') : denOf q' ≤ denOf q := by
  have := Nat.mul_le_mul_left (scanM - 1) (LmaxOf_mono h)
  unfold denOf
  omega

/-! ### The cap term at the start -/

theorem pow_le_cap (n : ℕ) (hn : 0 < n) : (1 + 1 / (n : ℝ)) ^ n ≤ (65 / 64 : ℝ) ^ 65 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
    have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
  have h2 : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
    calc (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / (n : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have h3 : Real.exp 1 ≤ (65 / 64 : ℝ) ^ 65 := by
    refine le_trans Real.exp_one_lt_d9.le ?_
    norm_num
  exact h2.trans h3

/-- **The cap term at the start is negligible**: `lam (LmaxOf q) 0 q ≤ (64/65)^(2^15)`. -/
theorem lam_start (q : ℕ) : lam (LmaxOf q) 0 q ≤ ENNReal.ofReal ((64 / 65 : ℝ) ^ (2 ^ 15 : ℕ)) := by
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  set n := 64 * scanM with hn
  have hn0 : 0 < n := by have := scanM_pos; omega
  set A := (q + n - 1) / n with hA
  have hqA : q ≤ n * A := by
    have h1 := Nat.div_add_mod (q + n - 1) n
    have h2 := Nat.mod_lt (q + n - 1) hn0
    rw [← hA] at h1
    omega
  have hx : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hreal : (1 + 1 / (n : ℝ)) ^ q * (64 / 65 : ℝ) ^ (65 * A + 2 ^ 15) ≤ (64 / 65 : ℝ) ^ (2 ^ 15 : ℕ) := by
    have h1 : (1 + 1 / (n : ℝ)) ^ q ≤ ((65 / 64 : ℝ) ^ 65) ^ A := by
      calc (1 + 1 / (n : ℝ)) ^ q ≤ (1 + 1 / (n : ℝ)) ^ (n * A) := pow_le_pow_right₀ hx hqA
        _ = ((1 + 1 / (n : ℝ)) ^ n) ^ A := pow_mul _ _ _
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (pow_le_cap n hn0) A
    calc (1 + 1 / (n : ℝ)) ^ q * (64 / 65 : ℝ) ^ (65 * A + 2 ^ 15)
        ≤ ((65 / 64 : ℝ) ^ 65) ^ A * (64 / 65 : ℝ) ^ (65 * A + 2 ^ 15) := by gcongr
      _ = ((65 / 64 : ℝ) * (64 / 65)) ^ (65 * A) * (64 / 65 : ℝ) ^ (2 ^ 15 : ℕ) := by
          rw [← pow_mul, pow_add, mul_pow]; ring
      _ = _ := by norm_num
  have hland : (1 : ℝ≥0∞) + landing / 64 = ENNReal.ofReal (1 + 1 / (n : ℝ)) := by
    rw [landing_eq_M, ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]
    congr 1
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by norm_num, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    congr 1
    rw [hn]
    push_cast
    field_simp
  have h64 : ((64 : ℝ≥0∞) / 65) = ENNReal.ofReal (64 / 65) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  unfold lam LmaxOf
  rw [pow_zero, one_mul, hland, h64, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

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

end Sphincs.Security.H0
