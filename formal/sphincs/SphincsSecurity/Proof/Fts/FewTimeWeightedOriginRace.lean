import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.IdealStatement

/-! ## FewTimeParametricSignerRace -/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem digestRaceSuccessRate_ne_zero_of_budget_lt
    (budget : Nat) (hbudget : budget < 2 ^ randomnessBits) :
    (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≠ 0 := by
  have hfraction : (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, ENNReal.div_lt_iff (by left; positivity) (by left; finiteness), one_mul]
    exact_mod_cast hbudget
  exact mul_ne_zero (ne_of_gt (tsub_pos_iff_lt.mpr hfraction)) (ENNReal.inv_ne_zero.mpr (by finiteness))

end SphincsSecurity

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def digestReuseWeight (q : Nat) : ℝ≥0∞ :=
  ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ /
    ((1 - ((q + digestAttemptLimit : Nat) : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹)

theorem digestReuseWeight_ne_top (q : Nat) (hq : q ≤ 2 ^ 127) :
    digestReuseWeight q ≠ ∞ := by
  apply ENNReal.div_ne_top (by finiteness)
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega

end Concrete

end SphincsSecurity
