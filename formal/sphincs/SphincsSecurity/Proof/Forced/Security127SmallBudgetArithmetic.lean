import SphincsSecurity.Proof.Fts.CertificateCacheExceptionGrowth
namespace SphincsSecurity.Concrete

open ENNReal

/-- The per-slot bound on the forced FTS near-certificate probability at hash budget `budget`: fourteen omitted trees, each paying the average terminal certificate price, the cache exception and the proposal prefix exception. -/
noncomputable def nearCertificateBound (budget : Nat) : ENNReal :=
  14 * ((budget : ENNReal) * (((557 : ENNReal) / 14) / (2 ^ 128 : Nat)) +
    ((budget : ENNReal) * certificateCacheExceptionRate + (2 ^ 700 : ENNReal)⁻¹))

set_option exponentiation.threshold 1024

private theorem smallRangeClosing (x : ℝ) (hlow : 1 / 2 ^ 128 ≤ x) (hhigh : x ≤ 3 / 16384) :
    7 / 4 * x + 11 / 65536 * x + 1 / 2 ^ 700 + x ^ 2 * 2 +
      16384 / 16381 * x * (557 * x + 14 * (x / 2 ^ 41) + 14 / 2 ^ 700) ≤ 2 * x := by
  have hn : 0 ≤ x := le_trans (by positivity) hlow
  have hsq : x * x ≤ x * (3 / 16384) := mul_le_mul_of_nonneg_left hhigh hn
  have htail : (1 : ℝ) / 2 ^ 700 ≤ x / 2 ^ 572 := by
    calc
      (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by norm_num
      _ ≤ x / 2 ^ 572 := div_le_div_of_nonneg_right hlow (by positivity)
  norm_num at hsq htail ⊢
  nlinarith [hsq, htail, hn, hlow, hhigh]

theorem small_bound_le_security127 (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ 3 * 2 ^ 114) :
    (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      (2 ^ 700 : ENNReal)⁻¹ + ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ((q : ENNReal) * nearCertificateBound q) ≤ (q : ENNReal) / 2 ^ 127 := by
  have hx : (q : ENNReal) / 2 ^ 128 ≤ 3 / 16384 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofNat]
    have hq' : (q : ℝ) ≤ 3 * 2 ^ 114 := by exact_mod_cast hsmall
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hhalf : (2 : ENNReal)⁻¹ ≤ 1 - (q : ENNReal) / 2 ^ 128 := by
    refine le_trans ?_ (tsub_le_tsub_left hx 1)
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]) (by finiteness)]
    norm_num [ENNReal.toReal_div, ENNReal.toReal_inv]
  have hsquare : ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) ≤ ((q : ENNReal) / 2 ^ 128) ^ 2 * 2 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inr (by finiteness)) (Or.inl (by finiteness)), mul_assoc]
    apply le_trans (le_of_eq (mul_one _).symm)
    apply mul_le_mul' le_rfl
    calc
      (1 : ENNReal) = 2 * (2 * ((2 : ENNReal)⁻¹) ^ 2) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl (pow_le_pow_left' hhalf 2))
  have hinv : ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ ≤ (16381 * 2 ^ 114 : ENNReal)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    have h : ((16381 * 2 ^ 114 : Nat) : ENNReal) ≤ ((2 ^ 128 - q : Nat) : ENNReal) := by
      exact_mod_cast (show 16381 * 2 ^ 114 ≤ 2 ^ 128 - q by omega)
    exact_mod_cast h
  have hrate : nearCertificateBound q ≤
      14 * ((q : ENNReal) * (((557 : ENNReal) / 14) / (2 ^ 128 : Nat)) +
        ((q : ENNReal) * (2 ^ 169 : ENNReal)⁻¹ + (2 ^ 700 : ENNReal)⁻¹)) := by
    unfold nearCertificateBound
    gcongr
    exact certificateCacheExceptionRate_le
  refine le_trans (add_le_add (add_le_add le_rfl hsquare) (mul_le_mul' hinv (mul_le_mul' le_rfl hrate))) ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hlow : 1 / 2 ^ 128 ≤ (q : ℝ) / 2 ^ 128 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hq
  have hhigh : (q : ℝ) / 2 ^ 128 ≤ 3 / 16384 := by
    have hq' : (q : ℝ) ≤ 3 * 2 ^ 114 := by exact_mod_cast hsmall
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  convert smallRangeClosing ((q : ℝ) / 2 ^ 128) hlow hhigh using 1 <;> ring

end SphincsSecurity.Concrete
