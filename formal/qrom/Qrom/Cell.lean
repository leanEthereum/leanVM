module

public import VCVio.Quantum.Oracle.Compressed.Basic
public import QuantumFoundations.MatrixMap.OpNorm

@[expose] public section

/-!
# The compression of one cell almost fixes the projector onto good values

On one cell `ℂ^(Option Y)`, let `G` project onto the values `y` with `good y`, a set of `s` of the
`N = |Y|` values, and let `c` be the one-cell compression (`Quantum.cellCompress`). Then
`‖c G c - G‖ ≤ 2 √(s / N)` (`Qrom.norm_conj_cellGood_sub_le`): conjugating by `c` moves the
projector by the square root of the density of good values.

The proof bounds the commutator by its Frobenius norm. Since `G` is diagonal, the entry of
`c G - G c` at `(a, b)` is `c a b (g b - g a)`, nonzero only between a good and a non-good index:
`‖[c, G]‖² ≤ 2 s / N + 2 s (N - s) / N² ≤ 4 s / N`. Then `c G c - G = [c, G] c` and `c` is unitary.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The diagonal indicator of the good values of one cell: `0` at the empty cell, `1` at a value
`y` with `good y`. -/
def cellGoodFn (good : Y → Prop) [DecidablePred good] : Option Y → ℂ
  | none => 0
  | some y => if good y then 1 else 0

/-- The projector onto the good values of one cell. -/
noncomputable def cellGood (good : Y → Prop) [DecidablePred good] :
    Matrix (Option Y) (Option Y) ℂ :=
  diagonal (cellGoodFn good)

theorem cellGoodFn_mem (good : Y → Prop) [DecidablePred good] (o : Option Y) :
    cellGoodFn good o = 0 ∨ cellGoodFn good o = 1 := by
  rcases o with _ | y
  · simp [cellGoodFn]
  · by_cases h : good y <;> simp [cellGoodFn, h]

/-- The squared norm of `g b - g a` for a `0`/`1` indicator: `1` exactly when they differ. -/
theorem norm_sub_cellGoodFn_sq (good : Y → Prop) [DecidablePred good] (a b : Option Y) :
    ‖cellGoodFn good b - cellGoodFn good a‖ ^ 2 =
      if cellGoodFn good a = cellGoodFn good b then 0 else 1 := by
  rcases cellGoodFn_mem good a with ha | ha <;> rcases cellGoodFn_mem good b with hb | hb <;>
    simp [ha, hb]

theorem cellCompress_mul_cellGood_sub_apply (good : Y → Prop) [DecidablePred good]
    (a b : Option Y) :
    (cellCompress Y * cellGood good - cellGood good * cellCompress Y) a b =
      cellCompress Y a b * (cellGoodFn good b - cellGoodFn good a) := by
  simp only [cellGood, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

variable [Nonempty Y]

/-- **The commutator bound.** `‖[c, G]‖² ≤ 4 s / N`. -/
theorem norm_cellCompress_comm_sq_le (good : Y → Prop) [DecidablePred good] :
    ‖cellCompress Y * cellGood good - cellGood good * cellCompress Y‖ ^ 2 ≤
      4 * ((Finset.univ.filter good).card : ℝ) / Fintype.card Y := by
  set N : ℝ := (Fintype.card Y : ℝ) with hN
  set s : ℝ := ((Finset.univ.filter good).card : ℝ) with hs
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hsN : s ≤ N := Nat.cast_le.mpr (Finset.card_le_univ _)
  have hamp : ‖cellAmp Y‖ ^ 2 = N⁻¹ := by
    have := cellAmp_mul_self Y
    rw [cellAmp] at this ⊢
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hNpos.le]
  have hinv : ‖((Fintype.card Y : ℂ))⁻¹‖ ^ 2 = N⁻¹ ^ 2 := by
    rw [norm_inv, Complex.norm_natCast]
  have hval : ∀ y x : Y, y ≠ x →
      ‖(if y = x then (1 : ℂ) else 0) - (Fintype.card Y : ℂ)⁻¹‖ ^ 2 = N⁻¹ ^ 2 := by
    intro y x hyx
    simp only [hyx, ↓reduceIte, zero_sub, norm_neg, norm_inv, Complex.norm_natCast, N]
  refine (l2_opNorm_sq_le_sum_sq _).trans ?_
  simp only [cellCompress_mul_cellGood_sub_apply, norm_mul, mul_pow, norm_sub_cellGoodFn_sq]
  -- the sum over pairs of cells with different indicators
  have hrow_none : ∑ b, ‖cellCompress Y none b‖ ^ 2 *
      (if cellGoodFn good none = cellGoodFn good b then 0 else 1) = s / N := by
    rw [Fintype.sum_option]
    simp only [cellCompress_none_none, cellCompress_none_some, hamp, cellGoodFn]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      zero_add]
    rw [hs, Finset.card_filter, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases hy : good y <;> simp [hy, mul_comm]
  have hrow_some : ∀ y, ∑ b, ‖cellCompress Y (some y) b‖ ^ 2 *
      (if cellGoodFn good (some y) = cellGoodFn good b then 0 else 1) ≤
      if good y then N⁻¹ + (N - s) * N⁻¹ ^ 2 else s * N⁻¹ ^ 2 := by
    intro y
    rw [Fintype.sum_option]
    simp only [cellCompress_some_none, cellCompress_some_some, hamp]
    by_cases hy : good y
    · simp only [cellGoodFn, hy, ite_true]
      simp only [one_ne_zero, ite_false, mul_one]
      refine add_le_add le_rfl ?_
      calc ∑ x, ‖(if y = x then (1 : ℂ) else 0) - (Fintype.card Y : ℂ)⁻¹‖ ^ 2 *
            (if (1 : ℂ) = if good x then 1 else 0 then 0 else 1)
          ≤ ∑ x, (if good x then 0 else N⁻¹ ^ 2) := Finset.sum_le_sum fun x _ ↦ by
            by_cases hx : good x
            · simp [hx]
            · have hyx : y ≠ x := fun h ↦ hx (h ▸ hy)
              rw [hval y x hyx]
              simp [hx]
        _ = (N - s) * N⁻¹ ^ 2 := by
            rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
              Finset.filter_not, Finset.card_univ_sdiff, Nat.cast_sub (Finset.card_le_univ _)]
    · simp only [cellGoodFn, hy, ite_false]
      simp only [ite_true, mul_zero, zero_add]
      calc ∑ x, ‖(if y = x then (1 : ℂ) else 0) - (Fintype.card Y : ℂ)⁻¹‖ ^ 2 *
            (if (0 : ℂ) = if good x then 1 else 0 then 0 else 1)
          ≤ ∑ x, (if good x then N⁻¹ ^ 2 else 0) := Finset.sum_le_sum fun x _ ↦ by
            by_cases hx : good x
            · have hyx : y ≠ x := fun h ↦ hy (h ▸ hx)
              rw [hval y x hyx]
              simp [hx]
            · simp [hx]
        _ = s * N⁻¹ ^ 2 := by
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.sum_option, hrow_none]
  calc s / N + ∑ y, ∑ b, ‖cellCompress Y (some y) b‖ ^ 2 *
        (if cellGoodFn good (some y) = cellGoodFn good b then 0 else 1)
      ≤ s / N + ∑ y, (if good y then N⁻¹ + (N - s) * N⁻¹ ^ 2 else s * N⁻¹ ^ 2) :=
        add_le_add le_rfl (Finset.sum_le_sum fun y _ ↦ hrow_some y)
    _ = s / N + (s * (N⁻¹ + (N - s) * N⁻¹ ^ 2) + (N - s) * (s * N⁻¹ ^ 2)) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
          Finset.filter_not, Finset.card_univ_sdiff, Nat.cast_sub (Finset.card_le_univ _)]
    _ ≤ 4 * s / N := by
        have h1 : (N - s) * N⁻¹ ^ 2 ≤ N⁻¹ := by
          rw [sq, ← mul_assoc]
          exact mul_le_of_le_one_left (inv_nonneg.mpr hNpos.le)
            (by rw [mul_inv_le_iff₀ hNpos]; linarith [hs ▸ (Nat.cast_nonneg _ : (0 : ℝ) ≤ s)])
        have hs0 : 0 ≤ s := Nat.cast_nonneg _
        have h2 : (N - s) * (s * N⁻¹ ^ 2) ≤ s * N⁻¹ := by
          have := mul_le_mul_of_nonneg_left h1 hs0
          nlinarith [this]
        have h3 : s * (N⁻¹ + (N - s) * N⁻¹ ^ 2) ≤ 2 * (s * N⁻¹) := by
          nlinarith [mul_le_mul_of_nonneg_left h1 hs0]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith

/-- **The one-cell bound.** `‖c G c - G‖ ≤ 2 √(s / N)`. -/
theorem norm_conj_cellGood_sub_le (good : Y → Prop) [DecidablePred good] :
    ‖cellCompress Y * cellGood good * cellCompress Y - cellGood good‖ ≤
      2 * √(((Finset.univ.filter good).card : ℝ) / Fintype.card Y) := by
  have hc : (cellCompress Y)ᴴ * cellCompress Y = 1 := by
    rw [conjTranspose_cellCompress, cellCompress_mul_self]
  have heq : cellCompress Y * cellGood good * cellCompress Y - cellGood good =
      (cellCompress Y * cellGood good - cellGood good * cellCompress Y) * cellCompress Y := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (cellGood good), cellCompress_mul_self, Matrix.mul_one]
  rw [heq]
  refine (l2_opNorm_mul _ _).trans ?_
  have hc1 : ‖cellCompress Y‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self hc
  have hcomm := norm_cellCompress_comm_sq_le good
  have hsq : ‖cellCompress Y * cellGood good - cellGood good * cellCompress Y‖ ≤
      2 * √(((Finset.univ.filter good).card : ℝ) / Fintype.card Y) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num), ← mul_div_assoc]
    exact Real.le_sqrt_of_sq_le hcomm
  calc _ ≤ 2 * √(((Finset.univ.filter good).card : ℝ) / Fintype.card Y) * 1 :=
        mul_le_mul hsq hc1 (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

end Qrom
