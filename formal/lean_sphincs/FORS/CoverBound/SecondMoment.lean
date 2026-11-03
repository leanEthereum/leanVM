import FORS.CoverBound.FirstMoment

/-! **The second per-tree moment.** The square of the cover fraction is the average over pairs of
target leaves of the product of their cover indicators. Two leaves are both disclosed by `n` uniform
leaves with probability `1 - 2 (1 - 1/A)^n + (1 - |{t, t'}|/A)^n`, so
`Ψ2(n) = 1 - 2 (1 - 1/A)^n + ((1 - 1/A)^n + (A - 1) (1 - 2/A)^n) / A`. -/

open ENNReal

namespace FORS.Security.H0

variable [Params]

open Concrete

set_option linter.unusedSectionVars false

/-- The second moment of the cover fraction of one tree after `n` uniform disclosed leaves. -/
noncomputable def Ψ2R (n : ℕ) : ℝ :=
  avgNR (fun X : Multiset FLeaf => (avgR fun t : FLeaf => coverR t X) ^ 2) n 0

theorem avgR_sq {α : Type} [Fintype α] (g : α → ℝ) :
    (avgR g) ^ 2 = avgR fun t => avgR fun t' => g t * g t' := by
  unfold avgR
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Two target leaves are both disclosed with probability `1 - 2 (1 - 1/A)^n + r^n`. -/
theorem avgNR_coverR_mul (t t' : FLeaf) (n : ℕ) :
    avgNR (fun Y => coverR t Y * coverR t' Y) n 0 =
      1 - 2 * (1 - 1 / leavesR) ^ n + avgR (fun x => missR t x * missR t' x) ^ n := by
  have h : (fun Y => coverR t Y * coverR t' Y) = fun Y => ((1 + (-1) * (Y.map (missR t)).prod) +
      (-1) * (Y.map (missR t')).prod) + (Y.map fun x => missR t x * missR t' x).prod := by
    funext Y
    rw [coverR_eq, coverR_eq, Multiset.prod_map_mul]
    ring
  rw [h, avgNR_add, avgNR_add, avgNR_add, avgNR_const, avgNR_const_mul, avgNR_const_mul, avgNR_prod_map,
    avgNR_prod_map, avgNR_prod_map, avgR_missR, avgR_missR]
  simp only [Multiset.map_zero, Multiset.prod_zero, one_mul]
  ring

theorem avgR_ite (t : FLeaf) (a b : ℝ) :
    avgR (fun t' : FLeaf => if t' = t then a else b) = (a + (leavesR - 1) * b) / leavesR := by
  unfold avgR
  have h : ∀ t' : FLeaf, (if t' = t then a else b) = b + (a - b) * if t' = t then 1 else 0 := fun t' => by
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_ind, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_fleaf]
  have := leavesR_pos
  field_simp
  ring

/-- **`Ψ2(n) = 1 - 2 (1 - 1/A)^n + ((1 - 1/A)^n + (A - 1) (1 - 2/A)^n) / A`.** -/
theorem Ψ2R_eq (n : ℕ) : Ψ2R n = 1 - 2 * (1 - 1 / leavesR) ^ n +
    ((1 - 1 / leavesR) ^ n + (leavesR - 1) * (1 - 2 / leavesR) ^ n) / leavesR := by
  unfold Ψ2R
  simp only [avgR_sq]
  rw [avgNR_avgR]
  simp only [avgNR_avgR, avgNR_coverR_mul, avgR_missR_mul]
  have hin : ∀ t : FLeaf, (avgR fun t' : FLeaf => 1 - 2 * (1 - 1 / leavesR) ^ n +
      (if t' = t then 1 - 1 / leavesR else 1 - 2 / leavesR) ^ n) =
      1 - 2 * (1 - 1 / leavesR) ^ n +
        ((1 - 1 / leavesR) ^ n + (leavesR - 1) * (1 - 2 / leavesR) ^ n) / leavesR := by
    intro t
    rw [avgR_add, avgR_const]
    congr 1
    rw [← avgR_ite t]
    congr 1
    funext t'
    split_ifs <;> rfl
  simp only [hin]
  exact avgR_const _

end FORS.Security.H0
