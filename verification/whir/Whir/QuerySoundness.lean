import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace Whir.QuerySoundness

open scoped BigOperators

/-- Product of coset densities for one independent stratified query per coset. -/
def missProduct {I : Type*} [Fintype I] (density : I → ℝ) : ℝ := ∏ i, density i

/-- Annex B's AM-GM step, valid even if a coset density is zero. -/
theorem strata_amgm {I : Type*} [Fintype I] [Nonempty I]
    (density : I → ℝ) (nonneg : ∀ i, 0 ≤ density i) :
    missProduct density ≤ ((∑ i, density i) / Fintype.card I) ^ Fintype.card I := by
  classical
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : I => (1 : ℝ)) density
    (by simp) (by simpa using hc) (fun i _ => nonneg i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, one_mul] at h
  have raised := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => nonneg i)) _) h
    (Fintype.card I)
  simpa only [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => nonneg i))
    (Nat.ne_of_gt Fintype.card_pos), missProduct] using raised

/-- A group can repeat every coset equally, including when query count exceeds domain size.
The repeated draws remain independent, not deduplicated. -/
theorem group_miss_bound {I : Type*} [Fintype I] [Nonempty I]
    (density : I → ℝ) (nonneg : ∀ i, 0 ≤ density i) (repetitions : ℕ) :
    missProduct density ^ repetitions ≤
      ((∑ i, density i) / Fintype.card I) ^ (Fintype.card I * repetitions) := by
  have h := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => nonneg i))
    (strata_amgm density nonneg) repetitions
  simpa only [pow_mul, missProduct] using h

/-- Independent binary groups' query counts add in the exponent. -/
theorem batch_miss_bound {G : Type*} [Fintype G]
    (miss : G → ℝ) (counts : G → ℕ) (density : ℝ)
    (nonneg : ∀ g, 0 ≤ miss g) (bounds : ∀ g, miss g ≤ density ^ counts g) :
    (∏ g, miss g) ≤ density ^ (∑ g, counts g) := by
  classical
  calc
    _ ≤ ∏ g, density ^ counts g :=
      Finset.prod_le_prod₀ (fun g _ => nonneg g) (fun g _ => bounds g)
    _ = _ := (Finset.prod_pow_eq_pow_sum ..)

end Whir.QuerySoundness
