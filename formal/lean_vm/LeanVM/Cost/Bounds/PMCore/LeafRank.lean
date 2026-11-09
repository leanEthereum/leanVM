module

public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Measure
public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeLeaf
public import LeanVM.Parameters.Field

/-!
# The leaf's pivot table: a rank potential

At order one the leaf's rows are `X^e·v`, `e ≤ 1`, of width `r` (`LeanVM.Extraction.Fast.PMDegree.HomRowLe 1`, closed under
the leaf's cancellations: `PMDegree.homRowLe_cancelClosed`). CompPoly's shifted row measure
(`shiftedRowMeasure`: the shifted degree times `r + 1`, plus the leading position plus one, `0` for
a zero row) of such a row takes one of at most `2·r` values (`measureSet`: `(e + shift_p)·(r + 1) +
p + 1`, `e ≤ 1`, `p < r`; **`measure_mem`**). Its **rank** `rk` (the values of `measureSet` at most
its measure) is at most `2·r` (**`rk_le`**) and strictly decreases with the measure
(**`rk_lt`**). Every cancellation of the pivot table lowers a measure (CompPoly's
`cancelShiftedLeadingTerm_shiftedRowMeasure_lt`), so the sum of the ranks of the table's rows and
the row being inserted drops at each cancellation: the cancellations over a whole leaf are at most
the ranks of the rows inserted, `≤ 2·r` each.
-/

namespace LeanVM.Cost.Bounds.PMCore

open CompPoly CompPoly.PolynomialMatrix LeanVM.Parameters

public section

/-- The measures of the rows `X^e·v`, `e ≤ 1`, of width `r`. -/
@[expose] def measureSet (r : ℕ) (shift : Array ℕ) : Finset ℕ :=
  ((Finset.range 2) ×ˢ (Finset.range r)).image fun x ↦ (x.1 + shift.getD x.2 0) * (r + 1) + x.2 + 1

theorem card_measureSet_le (r : ℕ) (shift : Array ℕ) : (measureSet r shift).card ≤ 2 * r := by
  unfold measureSet
  refine Finset.card_image_le.trans ?_
  simp

/-- **The rank of a row**: the values of `measureSet` at most its measure. -/
@[expose] def rk (r : ℕ) (shift : Array ℕ) (row : PolynomialRow K) : ℕ :=
  ((measureSet r shift).filter (· ≤ shiftedRowMeasure row shift)).card

theorem rk_le (r : ℕ) (shift : Array ℕ) (row : PolynomialRow K) : rk r shift row ≤ 2 * r :=
  (Finset.card_filter_le _ _).trans (card_measureSet_le r shift)

/-- **A row `X^e·v` of width `r` has its measure in `measureSet`, or is zero.** -/
theorem measure_mem {r : ℕ} {shift : Array ℕ} {row : PolynomialRow K} (hsize : row.size = r)
    (hh : LeanVM.Extraction.Fast.PMDegree.HomRowLe 1 row) :
    shiftedRowMeasure row shift = 0 ∨ shiftedRowMeasure row shift ∈ measureSet r shift := by
  unfold shiftedRowMeasure
  cases hdeg : rowShiftedDegree? row shift with
  | none => simp
  | some degree =>
    cases hpos : rowShiftedLeadingPosition? row shift with
    | none => simp
    | some pos =>
      right
      simp only
      have hentry := rowShiftedLeadingPosition?_entry_eq hdeg hpos
      obtain ⟨-, hd⟩ := shiftedEntryDegree?_eq_some_iff_data.1 hentry
      have hlt := rowShiftedLeadingPosition?_lt hpos
      have h1 := hh.natDegree_le pos
      unfold measureSet
      refine Finset.mem_image.2 ⟨((rowGet row pos).natDegree, pos), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]; omega
      · simp only; rw [hd, hsize]; ring

/-- A row with a leading term has a positive measure. -/
theorem measure_pos_of_leadingTerm {shift : Array ℕ} {row : PolynomialRow K}
    {t : ShiftedLeadingTerm K} (ht : rowShiftedLeadingTerm? row shift = some t) :
    0 < shiftedRowMeasure row shift := by
  obtain ⟨hd, hp, -⟩ := rowShiftedLeadingTerm?_some_data ht
  simp only [shiftedRowMeasure, hd, hp]
  omega

/-- **The rank decreases with the measure.** -/
theorem rk_lt {r : ℕ} {shift : Array ℕ} {new old : PolynomialRow K}
    (hlt : shiftedRowMeasure new shift < shiftedRowMeasure old shift)
    (hmem : shiftedRowMeasure old shift ∈ measureSet r shift) : rk r shift new < rk r shift old := by
  unfold rk
  refine Finset.card_lt_card ⟨fun x hx ↦ ?_, fun hsub ↦ ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  · have := hsub (Finset.mem_filter.2 ⟨hmem, le_rfl⟩)
    simp only [Finset.mem_filter] at this
    omega

/-- A row with a leading term, `X^e·v` of width `r`: its measure is in `measureSet`. -/
theorem measure_mem_of_leadingTerm {r : ℕ} {shift : Array ℕ} {row : PolynomialRow K}
    (hsize : row.size = r) (hh : LeanVM.Extraction.Fast.PMDegree.HomRowLe 1 row) {t : ShiftedLeadingTerm K}
    (ht : rowShiftedLeadingTerm? row shift = some t) :
    shiftedRowMeasure row shift ∈ measureSet r shift := by
  rcases measure_mem (shift := shift) hsize hh with h | h
  · have := measure_pos_of_leadingTerm ht; omega
  · exact h

end

end LeanVM.Cost.Bounds.PMCore
