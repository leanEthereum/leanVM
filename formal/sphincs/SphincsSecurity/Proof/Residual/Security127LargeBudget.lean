import SphincsSecurity.Proof.Residual.RetainedResidualCacheTail
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

private theorem largeRangeClosing (x : ℝ) (hx : 3 / 16384 ≤ x) :
    2 * x - x ^ 2 + (11 / 65536) * x + (x / 2 ^ 41 + 1 / 2 ^ 700) ≤ 2 * x := by
  have hn : 0 ≤ x := le_trans (by norm_num) hx
  have hs := mul_nonneg (sub_nonneg.mpr hx) hn
  have he : (1 : ℝ) / 2 ^ 700 ≤ 1 / 1099511627776 := by
    calc
      _ ≤ 1 / (2 : ℝ) ^ 40 := one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by decide : 40 ≤ 700))
      _ = _ := by norm_num
  apply le_trans (add_le_add le_rfl (add_le_add le_rfl he))
  norm_num at hx hs ⊢
  nlinarith

theorem native_bound_le_security127 (q : Nat) (hlarge : 3 * 2 ^ 114 ≤ q) (hsmall : q ≤ 2 ^ 127) :
    ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2) +
      (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      ((q : ENNReal) * (2 ^ 169 : ENNReal)⁻¹ + (2 ^ 700 : ENNReal)⁻¹) ≤ (q : ENNReal) / 2 ^ 127 := by
  let x : ℝ := (q : ℝ) / 2 ^ 128
  have hx : 3 / 16384 ≤ x := by
    have hq : (3 * 2 ^ 114 : ℝ) ≤ q := by exact_mod_cast hlarge
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num at hq ⊢
    exact hq
  have hn : 0 ≤ x := by positivity
  have hu : x ≤ 1 / 2 := by
    have hq : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hsmall
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num at hq ⊢
    exact hq
  have hp : 0 ≤ 2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2 := by
    change 0 ≤ 2 * x - x ^ 2
    nlinarith
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  convert largeRangeClosing x hx using 1 <;> generalize (2 : ℝ) ^ 700 = tailDenominator <;> dsimp only [x, digestBits] <;> ring

theorem security127_of_large_budget (q : Nat) (hlarge : 3 * 2 ^ 114 ≤ q) (adversary : Adversary)
    (hcost : HasHashQueryBound scheme adversary q) : forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 127 := by
  by_cases hsmall : q ≤ 2 ^ 127
  · exact (RetainedResidual.forgeAdvantage_le_native_bound fixedReferenceDummy
      (fun _ _ _ => fixedReferenceDummyWord_valid) adversary q hcost hsmall).trans
        (native_bound_le_security127 q hlarge hsmall)
  · apply probOutput_le_one.trans
    calc
      (1 : ENNReal) = (2 ^ 127 : ENNReal) / 2 ^ 127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 2 ^ 127 ≤ q by omega)) _

end SphincsSecurity.Concrete
