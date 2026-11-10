module

public import VCVio.Quantum.Oracle.Compressed.Basic
public import QuantumFoundations.MatrixMap.OpNorm

@[expose] public section

/-!
# Norms of operators acting cell by cell

`Quantum.piKron A` acts on a table register `ι → Z` with the operator `A i` on the cell `i`. This
file proves that its operator norm is at most the product of the norms of the factors
(`Qrom.norm_piKron_le_prod`), and the telescoping bound: two such operators whose factors are
contractions differ by at most the sum of the norms of the differences of the factors
(`Qrom.norm_piKron_sub_le`).

The cell `z` splits off the table register (`Equiv.piSplitAt`): `piKron A` is `A z` tensored with
the operator on the other cells, reindexed (`Qrom.piKron_eq_submatrix_kronecker`).
-/

open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The norm of a tensor product is at most the product of the norms. -/
theorem norm_kronecker_le {m n p r : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype r]
    [DecidableEq n] [DecidableEq p] [DecidableEq r]
    (A : Matrix m n 𝕜) (B : Matrix p r 𝕜) : ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have h : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix p p 𝕜)) * ((1 : Matrix n n 𝕜) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have h1 : (1 : Matrix n n 𝕜) ⊗ₖ B =
      (B ⊗ₖ (1 : Matrix n n 𝕜)).submatrix (Equiv.prodComm n p) (Equiv.prodComm n r) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [kroneckerMap_apply, mul_comm]
  rw [h]
  refine (l2_opNorm_mul _ _).trans ?_
  refine mul_le_mul (l2_opNorm_kronecker_one_le A) ?_ (norm_nonneg _) (norm_nonneg _)
  rw [h1, l2_opNorm_submatrix_equiv]
  exact l2_opNorm_kronecker_one_le B

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]

/-- Splitting off the cell `z`: `piKron A` is `A z ⊗ piKron (A on the other cells)`. -/
theorem piKron_eq_submatrix_kronecker (A : ι → Matrix Z Z ℂ) (z : ι) :
    piKron A = (A z ⊗ₖ piKron (fun j : {j // j ≠ z} ↦ A j)).submatrix
      (Equiv.piSplitAt z fun _ ↦ Z) (Equiv.piSplitAt z fun _ ↦ Z) := by
  ext D D'
  simp only [piKron_apply, submatrix_apply, kroneckerMap_apply, Equiv.piSplitAt_apply]
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun i ↦ A i (D i) (D' i)) z

/-- **The product bound.** The norm of `piKron A` is at most the product of the norms of the
factors. -/
theorem norm_piKron_le_prod : ∀ (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι = n → ∀ A : ι → Matrix Z Z ℂ, ‖piKron A‖ ≤ ∏ i, ‖A i‖
  | 0, ι, _, _, h, A => by
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
    have h1 : piKron A = 1 := by
      ext D D'
      simp [piKron_apply, Matrix.one_apply, Subsingleton.elim D D']
    rw [h1, Finset.univ_eq_empty, Finset.prod_empty]
    exact l2_opNorm_one_le
  | n + 1, ι, _, _, h, A => by
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨z⟩ := ‹Nonempty ι›
    have hc : Fintype.card {j // j ≠ z} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    rw [piKron_eq_submatrix_kronecker A z, l2_opNorm_submatrix_equiv,
      Fintype.prod_eq_mul_prod_subtype_ne (fun i ↦ ‖A i‖) z]
    refine (norm_kronecker_le _ _).trans ?_
    exact mul_le_mul le_rfl (norm_piKron_le_prod n hc _) (norm_nonneg _) (norm_nonneg _)

theorem norm_piKron_le (A : ι → Matrix Z Z ℂ) : ‖piKron A‖ ≤ ∏ i, ‖A i‖ :=
  norm_piKron_le_prod _ rfl A

/-- `piKron` is additive in one factor. -/
theorem piKron_update_sub (A : ι → Matrix Z Z ℂ) (z : ι) (M M' : Matrix Z Z ℂ) :
    piKron (Function.update A z (M - M')) =
      piKron (Function.update A z M) - piKron (Function.update A z M') := by
  ext D D'
  simp only [piKron_apply, Matrix.sub_apply]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ z, Fintype.prod_eq_mul_prod_subtype_ne _ z,
    Fintype.prod_eq_mul_prod_subtype_ne _ z]
  simp only [Function.update_self, Matrix.sub_apply]
  have hrest : ∀ N : Matrix Z Z ℂ, (∏ j : {j // j ≠ z},
      Function.update A z N (j : ι) (D j) (D' j)) = ∏ j : {j // j ≠ z}, A j (D j) (D' j) :=
    fun N ↦ Finset.prod_congr rfl fun j _ ↦ by rw [Function.update_of_ne j.2]
  rw [hrest, hrest, hrest, sub_mul]

/-- **The telescoping bound.** If every factor of `A` and of `B` is a contraction, then
`‖piKron A - piKron B‖ ≤ ∑ i, ‖A i - B i‖`. -/
theorem norm_piKron_sub_le (A B : ι → Matrix Z Z ℂ) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hB : ∀ i, ‖B i‖ ≤ 1) : ‖piKron A - piKron B‖ ≤ ∑ i, ‖A i - B i‖ := by
  classical
  -- induction on the set of cells where the factors differ
  suffices h : ∀ S : Finset ι, ∀ C : ι → Matrix Z Z ℂ, (∀ i, ‖C i‖ ≤ 1) →
      (∀ i ∉ S, C i = B i) → ‖piKron C - piKron B‖ ≤ ∑ i ∈ S, ‖C i - B i‖ by
    refine (h Finset.univ A hA (by simp)).trans le_rfl
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro C _ hC
    rw [show C = B from funext fun i ↦ hC i (Finset.notMem_empty i)]
    simp
  | insert z S hz ih =>
    intro C hC hCB
    set C' := Function.update C z (B z) with hC'
    have hC'1 : ∀ i, ‖C' i‖ ≤ 1 := fun i ↦ by
      by_cases hi : i = z
      · subst hi; simpa [hC'] using hB i
      · simpa [hC', Function.update_of_ne hi] using hC i
    have hC'B : ∀ i ∉ S, C' i = B i := fun i hi ↦ by
      by_cases hiz : i = z
      · subst hiz; simp [hC']
      · rw [hC', Function.update_of_ne hiz]
        exact hCB i (by simp [hiz, hi])
    have hsplit : piKron C - piKron C' = piKron (Function.update C z (C z - B z)) := by
      rw [piKron_update_sub, Function.update_eq_self]
    have hfirst : ‖piKron C - piKron C'‖ ≤ ‖C z - B z‖ := by
      rw [hsplit]
      refine (norm_piKron_le _).trans ?_
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ z, Function.update_self]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      refine Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ ?_
      rw [Function.update_of_ne j.2]
      exact hC j
    have hrest : ∑ i ∈ S, ‖C' i - B i‖ = ∑ i ∈ S, ‖C i - B i‖ :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [hC', Function.update_of_ne (by rintro rfl; exact hz hi)]
    calc ‖piKron C - piKron B‖ = ‖(piKron C - piKron C') + (piKron C' - piKron B)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖piKron C - piKron C'‖ + ‖piKron C' - piKron B‖ := norm_add_le _ _
      _ ≤ ‖C z - B z‖ + ∑ i ∈ S, ‖C i - B i‖ :=
          add_le_add hfirst ((ih C' hC'1 hC'B).trans hrest.le)
      _ = ∑ i ∈ insert z S, ‖C i - B i‖ := by rw [Finset.sum_insert hz]

end Qrom
