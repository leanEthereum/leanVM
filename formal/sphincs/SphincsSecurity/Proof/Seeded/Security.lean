import SphincsSecurity.Proof.Seeded.GameComparison
import SphincsSecurity.Proof

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem seed_loss_absorbed (q : Nat) (hq : 1 ≤ q) (hsmall : q < 2 ^ 127) :
    ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
        q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hguess : ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
      1 / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
    calc
      _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div (by exact_mod_cast (Nat.sub_le q 1).trans hsmall.le) le_rfl
      _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) /
          (((2 ^ 127 : Nat) : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)) :=
        ENNReal.div_le_div le_rfl (by norm_num)
      _ = _ := by
        simpa only [mul_one] using ENNReal.mul_div_mul_left 1 ((2 ^ 127 : Nat) : ℝ≥0∞)
          (c := ((2 ^ 127 : Nat) : ℝ≥0∞)) (by norm_num) (ENNReal.natCast_ne_top _)
  calc
    _ ≤ ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
        1 / ((2 ^ 127 : Nat) : ℝ≥0∞) := add_le_add le_rfl hguess
    _ = _ := by
      rw [← ENNReal.add_div]
      congr 1
      exact_mod_cast Nat.sub_add_cancel hq

theorem scheme_has_127_bits_of_classical_security : HasClassicalSecurityBits scheme 127 := by
  intro q hq adversary hbound
  by_cases hsmall : q < 2 ^ 127
  · have hindependent := hashQueryBound_independent_from_seeded adversary q
      (hsmall.trans (by norm_num)) hbound
    have hcomparison := forgeAdvantage_seeded_le_of_independent_budget adversary (q - 1) hindependent
    by_cases hone : q = 1
    · subst q
      have hbudget : HasHashQueryBound Concrete.scheme adversary 1 := by
        rw [hasHashQueryBound_iff] at hindependent ⊢
        exact hindependent.mono (by decide)
      have hsecurity := Concrete.security127 1 (by decide)
        adversary hbudget
      simp only [Nat.sub_self, Nat.cast_zero, ENNReal.zero_div, add_zero] at hcomparison
      exact hcomparison.trans hsecurity
    · have hsecurity := Concrete.security127 (q - 1)
        (by omega) adversary hindependent
      exact hcomparison.trans ((add_le_add hsecurity le_rfl).trans (seed_loss_absorbed q hq hsmall))
  · have hlarge : 2 ^ 127 ≤ q := Nat.le_of_not_gt hsmall
    calc
      forgeAdvantage scheme adversary ≤ 1 := probOutput_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl

end SphincsSecurity.Seeded
