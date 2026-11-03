import FORS.CoverBound.Moments

/-! **The first per-tree moment.** The cover fraction of one tree, averaged over `n` independent
uniform disclosed leaves, is the probability that a target leaf is among them:
`Ψ1(n) = 1 - (1 - 1/A)^n`, `A = 2^a` the number of leaves. -/

open ENNReal

namespace FORS.Security.H0

variable [Params]

open Concrete

set_option linter.unusedSectionVars false

/-- The first moment of the cover fraction of one tree after `n` uniform disclosed leaves. -/
noncomputable def Ψ1R (n : ℕ) : ℝ := avgNR (fun X : Multiset FLeaf => avgR fun t : FLeaf => coverR t X) n 0

/-- A target leaf is disclosed by `n` uniform leaves with probability `1 - (1 - 1/A)^n`. -/
theorem avgNR_coverR (t : FLeaf) (n : ℕ) : avgNR (coverR t) n 0 = 1 - avgR (missR t) ^ n := by
  have h : coverR t = fun Y => 1 + (-1) * (Y.map (missR t)).prod := funext fun Y => by rw [coverR_eq]; ring
  rw [h, avgNR_add, avgNR_const, avgNR_const_mul, avgNR_prod_map]
  simp only [Multiset.map_zero, Multiset.prod_zero, one_mul]
  ring

/-- **`Ψ1(n) = 1 - (1 - 1/A)^n`.** -/
theorem Ψ1R_eq (n : ℕ) : Ψ1R n = 1 - (1 - 1 / leavesR) ^ n := by
  unfold Ψ1R
  rw [avgNR_avgR]
  simp only [avgNR_coverR, avgR_missR]
  exact avgR_const _

end FORS.Security.H0
