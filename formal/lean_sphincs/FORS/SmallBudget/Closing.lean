module

public import FORS.SmallBudget.SampleEvents

@[expose] public section

/-! **The deterministic signer at 127 bits.** Small budgets (`q - keygenCost ≤ qh`):
the sample bound averaged over the prepared samples, in closed form from one rational check
`checkSmallF` at the right end `qh`. Large budgets: the weighted one-coin bound from a checked chain
of covers of the budgets above `qh`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-! ### The closed form -/

/-- The coefficient of the failing share. -/
noncomputable def smallFailF (q : ℕ) : ℝ≥0∞ :=
  (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) * (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit)

/-- The sample-independent part of the small-budget bound. -/
noncomputable def smallMainFF (ρ : ℝ) (q : ℕ) (B c : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) + ((q - keygenCost : ℕ) : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) +
    ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) * ((q - keygenCost : ℕ) * ENNReal.ofReal (c : ℝ))

theorem one_le_keygenCostF : 1 ≤ keygenCost := by
  unfold keygenCost Prefix.keygenHashCost
  have : 1 ≤ 2 ^ keptHeight topLayer := Nat.one_le_two_pow
  omega

/-- The cap term at the start is below `2^-201`. -/
theorem lam_start_leF (q : ℕ) : lam (H0.LmaxOf q) 0 q ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
  refine le_trans (H0.lam_start q) ?_
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2 : ℝ) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h2]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (64 / 65 : ℝ) ^ (2 ^ 15 : ℕ) = ((64 / 65 : ℝ) ^ 64) ^ 512 := by rw [← pow_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) ^ 512 := pow_le_pow_left₀ (by norm_num) (by norm_num) 512
    _ ≤ (1 / 2 : ℝ) ^ 201 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)

/-- The real inequality behind the closed form. The coin term is `2^-128 · (x^2 / 2) (2 − 1/M) 2^-128`
(a unit of budget is a contact attempt or a digest query, so the pairs are counted once); the
two cap terms, each at most `2^-201`, are paid by the `2^-60` slack like the failing shares. -/
theorem small_realFF (x qh q N ρ B c M : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (_hB : 0 ≤ B) (hc : 0 ≤ c) (hM : 1 ≤ M)
    (hcheck : ρ + 2 ^ 128 * B + (2 * M - 1) * qh / (M * 2 ^ 129) + qh * c + 1 / 2 ^ 60 ≤ 2) :
    ρ * x / 2 ^ 128 + x * B + (2 ^ 128)⁻¹ * (x * x / 2 * ((2 - 1 / M) / 2 ^ 128)) + x * (2 ^ 128)⁻¹ * (x * c) +
        ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 + 2 * (1 / 2) ^ 201 + 3 * (q / 2 ^ 256) ≤
      q / 2 ^ 127 := by
  have hM0 : M ≠ 0 := by linarith
  have hr0 : 0 ≤ (2 - 1 / M) / 2 ^ 129 := by
    apply div_nonneg _ (by positivity)
    have : 1 / M ≤ 1 := by rw [div_le_one (by linarith)]; exact hM
    linarith
  have e : (2 * M - 1) * qh / (M * 2 ^ 129) = qh * ((2 - 1 / M) / 2 ^ 129) := by
    field_simp
  have e0 : (2 ^ 128 : ℝ)⁻¹ * (x * x / 2 * ((2 - 1 / M) / 2 ^ 128)) =
      x * (2 ^ 128)⁻¹ * (x * ((2 - 1 / M) / 2 ^ 129)) := by
    ring
  rw [e] at hcheck
  rw [e0]
  generalize (2 - 1 / M) / 2 ^ 129 = r at hr0 hcheck ⊢
  have h1 : x * r ≤ qh * r := mul_le_mul_of_nonneg_right hxq hr0
  have h2 : x * c ≤ qh * c := mul_le_mul_of_nonneg_right hxq hc
  have hbr : ρ + 2 ^ 128 * B + x * r + x * c ≤ 2 - 1 / 2 ^ 60 := by linarith
  have hmain : ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (x * r) + x * (2 ^ 128)⁻¹ * (x * c) =
      x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + x * r + x * c) := by
    field_simp
  have hmain' : x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + x * r + x * c) ≤
      x * (2 ^ 128)⁻¹ * (2 - 1 / 2 ^ 60) := mul_le_mul_of_nonneg_left hbr (by positivity)
  have hx1 : x * (2 ^ 128 : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    linarith
  have hfail : ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 ≤ (x + N) * 2 * (1 / 2) ^ 201 := by
    have : x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ x + N := by
      calc x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ 1 * (x + N) := mul_le_mul_of_nonneg_right hx1 (by positivity)
        _ = x + N := one_mul _
    have hp : (0 : ℝ) ≤ (1 / 2) ^ 201 := by positivity
    nlinarith
  have hq0 : 0 ≤ q := by linarith
  have e201 : ((1 : ℝ) / 2) ^ 201 = 1 / 2 ^ 201 := by rw [div_pow, one_pow]
  rw [hmain]
  rw [e201] at hfail ⊢
  have hxq' : x ≤ 2 ^ 127 := le_trans hxq hqh
  have key : x * (2 ^ 128)⁻¹ * (2 - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (1 / 2 ^ 201) +
      3 * (q / 2 ^ 256) ≤ q / 2 ^ 127 := by
    have ex : x * (2 ^ 128 : ℝ)⁻¹ * (2 - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (1 / 2 ^ 201) +
        3 * (q / 2 ^ 256) = (x * (2 ^ 129 - 2 ^ 68) + (x + N) * 2 ^ 56 + 2 ^ 56 + 3 * q) / 2 ^ 256 := by
      field_simp
    have ey : q / (2 : ℝ) ^ 127 = q * 2 ^ 129 / 2 ^ 256 := by
      field_simp
    rw [ex, ey]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    linarith
  linarith

set_option maxRecDepth 100000 in
/-- **The small-budget bound in closed form**, with the two cap terms of the scan signer. -/
theorem small_closeFF (q qh : ℕ) (hq1 : 1 ≤ q) (hq' : q - keygenCost ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hN : signatureLimit ≤ 2 ^ 70) (ρ : ℝ) (hρ : 0 ≤ ρ) (B c : ℚ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcheck : ρ + 2 ^ 128 * (B : ℝ) + (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
        qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2) :
    smallMainFF ρ q B c + smallFailF q * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) + 3 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  set q' := q - keygenCost with hq'def
  have hK : 1 ≤ keygenCost := one_le_keygenCostF
  have hq'1 : q' + 1 ≤ q := by omega
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hM : (1 : ℝ) ≤ (H0.scanM : ℝ) := by exact_mod_cast H0.scanM_pos
  have r1 : (q' : ℝ) ≤ qh := Nat.cast_le.mpr hq'
  have r2 : (qh : ℝ) ≤ 2 ^ 127 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hqh
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r3 : (q' : ℝ) + 1 ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq'1
    rwa [Nat.cast_add, Nat.cast_one] at h
  have r4 : (signatureLimit : ℝ) ≤ 2 ^ 70 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have hreal := small_realFF (q' : ℝ) qh q signatureLimit ρ B c (H0.scanM : ℝ) (Nat.cast_nonneg _)
    r1 r2 r3 (Nat.cast_nonneg _) r4 hB' hc' hM hcheck
  have hr0 : (0 : ℝ) ≤ (2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128 := by
    apply div_nonneg _ (by positivity)
    have : 1 / (H0.scanM : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM
    linarith
  have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by rw [ENNReal.ofReal_ofNat]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hq256 : (q : ℝ≥0∞) / 2 ^ 256 = ENNReal.ofReal (q / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  have hq127 : (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    norm_num
  refine le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_right (lam_start_leF q') 2)) le_rfl) ?_
  have hC : ((Nat.choose q' 2 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((q' : ℝ) * q' / 2) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Nat.cast_choose_two]
    have h0 : (0 : ℝ) ≤ (q' : ℝ) := Nat.cast_nonneg _
    nlinarith
  unfold smallMainFF smallFailF
  rw [← hq'def]
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul' le_rfl (mul_le_mul' hC le_rfl))) le_rfl) le_rfl) le_rfl) le_rfl) ?_
  rw [rateS_eqF, hhalf, hq256, hq127, ν_eq_ofReal, hnat q', hnat signatureLimit, h2, h3]
  generalize (2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128 = r at hr0 hreal ⊢
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The seed-free bound and the deterministic signer -/

/-! ### The rational check -/

/-- The rational small-route check at the right end `qh` of the small budgets: the coin term is
`(2 M − 1) qh / (M 2^129)` with `M = 2^(H − b)` (the creation rate of the scan signer), the near term
is multiplied by `κ = 2 - ρ + qh / 2^128 + N / (2^b 2^a)`. -/
def checkSmallF (H b a N qh : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide ((N : ℚ) / (2 ^ b * 2 ^ a) ≤ ρ - 1 - (qh : ℚ) / 2 ^ 128) &&
    decide (ρ + 2 ^ 128 * B + (2 * (H0.scanMb H b : ℚ) - 1) * (qh : ℚ) / ((H0.scanMb H b : ℚ) * 2 ^ 129) +
      (2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ a)) * qh * c + 1 / 2 ^ 60 ≤ 2)

theorem checkSmallF_sound {H b a N qh : ℕ} {ρ cthr B c : ℚ}
    (h : checkSmallF H b a N qh ρ cthr B c = true) :
    Numeric (ρ : ℝ) ((qh : ℝ) / 2 ^ 128) ∧ qh ≤ 2 ^ 127 ∧ N ≤ 2 ^ 70 ∧ (cthr : ℝ) ≤ (ρ : ℝ) / 2 ^ 128 ∧
      0 ≤ B ∧ 0 ≤ c ∧
      (N : ℝ) / (2 ^ b * 2 ^ a) ≤ (ρ : ℝ) - 1 - (qh : ℝ) / 2 ^ 128 ∧
      (ρ : ℝ) + 2 ^ 128 * (B : ℝ) + (2 * (H0.scanMb H b : ℝ) - 1) * (qh : ℝ) / ((H0.scanMb H b : ℝ) * 2 ^ 129) +
        (2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ a)) * qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
  simp only [checkSmallF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have r1 := (Rat.cast_le (K := ℝ)).mpr h1
  have r2 := (Rat.cast_le (K := ℝ)).mpr h2
  have r3 := (Rat.cast_le (K := ℝ)).mpr h3
  have r4 := (Rat.cast_le (K := ℝ)).mpr h4
  have r5 := (Rat.cast_le (K := ℝ)).mpr h5
  have r8 := (Rat.cast_le (K := ℝ)).mpr h8
  have r11 := (Rat.cast_le (K := ℝ)).mpr h11
  have r12 := (Rat.cast_le (K := ℝ)).mpr h12
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at r1 r2 r3 r4 r5 r8 r11 r12
  exact ⟨⟨r1, r2, r3, r4, r5⟩, h6, h7, r8, h9, h10, r11, r12⟩

end FORS.Security.ForsPotential
