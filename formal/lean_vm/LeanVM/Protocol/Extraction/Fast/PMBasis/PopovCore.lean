module

-- `coeff`, `ofArray` and friends are declared in bare `public section`s, so their
-- bodies are opaque downstream (as in CompPoly's `PMBasis/Correctness.lean`).
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
public import LeanVM.Protocol.Extraction.Fast.PMBasis.PopovLeaf

/-!
# The PM-basis on any sound leaf, and on the leaf sorted by pivot

CompPoly proves its recursive PM-basis (`pmBasisWithFuelCore`, `PMBasis/Recursion.lean`) sound and
complete for its kernel leaf only (`kernelLeafRuntimeWithLowAndCompose`); the proofs use two facts
of the leaf, its rows' soundness (`kernelLeafBasis_rows`) and its span's completeness
(`kernelLeafBasis_rowSpan_complete`). `leafRuntime` is CompPoly's runtime with any leaf, and
`leafRuntime_core_rows` / `leafRuntime_core_rowSpan_complete` are CompPoly's
`pmBasisWithFuelCore_kernelLeaf_rows` / `pmBasisWithFuelCore_kernelLeaf_rowSpan_complete`, their
proofs copied with the leaf's two facts as hypotheses (`LeafRows`, `LeafSpanComplete`).

On a leaf that is ordered weak Popov (`OrderedWeakPopov`, `PopovCompose.lean`), the core is ordered
weak Popov at every level (**`leafRuntime_core_orderedWeakPopov`**: induction, with the composition
lemma `orderedWeakPopov_mulWith` at each node), and the root normalization, CompPoly's full
weak-Popov pass `pmBasisNormalizeRoot`, is the identity on it
(**`pmBasisNormalizeRoot_of_orderedWeakPopov`**: each row lands in its own empty pivot slot, no
cancellation, and no position is missing). So **`pmBasis_leafRuntime_eq_core`**: the PM-basis is
its core, with no root pass at all.

`popovLeafBasis` (`PopovLeaf.lean`) is such a leaf, with CompPoly's two leaf facts carried over;
**`popovCorePMBasisContextWithLowAndCompose`** is CompPoly's `PMBasisContext` (sound, and
complete-minimal through the predictable-degree property of the core's weak Popov form) for the
PM-basis core on it.

Credits: the PM-basis, its correctness proofs (copied here, generalized over the leaf) and the
lemmas they use are CompPoly's (github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026
CompPoly Contributors", Valerii Huhnin).
-/

namespace LeanVM.Extraction.Fast.Popov

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open CompPoly.DenseMatrix (array_getD_of_le' array_getD_of_lt' array_getD_setIfInBounds)

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- CompPoly's PM-basis runtime (`kernelLeafRuntimeWithLowAndCompose`) with another leaf. -/
@[expose] def leafRuntime (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F) : PMBasisRuntime F where
  mulContext := mulCtx
  lowMulContext := lowCtx
  composeBasis := PolynomialMatrix.mulStrassenWith lowCtx composeLeafCutoff
  residualProduct := PolynomialMatrix.mulTruncColumnStrassenWith lowCtx composeLeafCutoff
  leafCutoff := leafCutoff
  leafBasis := leaf

/-- The leaf's rows approximate the problem, at its width. -/
@[expose] def LeafRows (mulCtx : CPolynomial.MulContext F)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F) : Prop :=
  ∀ (problem : XAdicProblem F) (shift : Array Nat),
    ∀ row ∈ MatrixRows (leaf problem shift),
      RowApproximates mulCtx problem row ∧ row.size = problem.matrix.size

/-- Every nonzero solution of the problem's width lies in the leaf's row span. -/
@[expose] def LeafSpanComplete (mulCtx : CPolynomial.MulContext F)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F) : Prop :=
  ∀ (problem : XAdicProblem F) (shift : Array Nat),
    0 < problem.matrix.size → WellFormed problem.matrix →
    ∀ {row : PolynomialRow F}, RowApproximates mulCtx problem row →
      row.size = problem.matrix.size → ¬ RowIsZero row →
      row ∈ RowSpan (leaf problem shift)

/-! ## CompPoly's core proofs, on any sound leaf -/

/-- Every row of the fuel-bounded PM-basis core on a sound leaf approximates the
problem and has the principal row width. -/
theorem leafRuntime_core_rows (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F)
    (hleafRows : LeafRows mulCtx leaf) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      ∀ row ∈ MatrixRows (pmBasisWithFuelCore
        (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel problem shift),
        RowApproximates mulCtx problem row ∧ row.size = problem.matrix.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift row hrow
      rw [pmBasisWithFuelCore] at hrow
      exact hleafRows problem shift row
        (compactNonzeroRows_subset hrow)
  | succ fuel ih =>
      intro problem shift row hrow
      rw [pmBasisWithFuelCore] at hrow
      split at hrow
      · exact hleafRows problem shift row
          (compactNonzeroRows_subset hrow)
      · set d₁ := maxOrder problem / 2 with hd₁
        set lower : XAdicProblem F :=
          { orders := lowerOrders problem d₁, matrix := problem.matrix } with hlower
        set P₁ := pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel lower shift with hP₁def
        set resOrders := residualOrders problem d₁ with hresOrders
        set Rmat := residualMatrixWithProduct
          (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
          problem.matrix d₁ resOrders with hRmatdef
        set residual : XAdicProblem F :=
          { orders := resOrders, matrix := Rmat } with hresidual
        set shifted := updateShiftByRows P₁ shift with hshifted
        set P₂ := pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel residual shifted with hP₂def
        have hrow2 : row ∈ MatrixRows (compactNonzeroRows
            (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁)) := hrow
        have hmem := compactNonzeroRows_subset hrow2
        have hnz := compactNonzeroRows_nonzero hrow2
        rw [mulStrassenWith_eq_mulWith, matrixRows_mulWith] at hmem
        rcases List.mem_map.mp hmem with ⟨p₂, hp₂mem, rfl⟩
        have hctx : rowMulMatrixWith lowCtx.mulContext p₂ P₁ =
            rowMulMatrixWith mulCtx p₂ P₁ := rowMulMatrixWith_ctx _ _ _ _
        rw [hctx] at hnz ⊢
        have hIH₁ : ∀ r ∈ MatrixRows P₁,
            RowApproximates mulCtx lower r ∧ r.size = problem.matrix.size :=
          fun r hr ↦ ih lower shift r hr
        have hIH₂ := ih residual shifted p₂ hp₂mem
        rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | hP₁0
        · exfalso
          have hP₁empty : P₁ = #[] := Array.eq_empty_of_size_eq_zero hP₁0
          have hsize0 : (rowMulMatrixWith mulCtx p₂ P₁).size = 0 := by
            rw [rowMulMatrixWith_size, hP₁empty]
            rfl
          rw [Array.eq_empty_of_size_eq_zero hsize0] at hnz
          simp [rowIsZero] at hnz
        · -- Shape facts for the residual matrix.
          have hprodsize : (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
              (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix).size =
                P₁.size := mulTruncColumnStrassenWith_size _ _ _ _ _
          have hRsize : Rmat.size = P₁.size := by
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [ofFn_size, hprodsize]
          have hprodwidth : 0 < P₁.size →
              MatrixWidth (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix) =
                MatrixWidth problem.matrix := by
            intro hpos
            rw [mulTruncColumnStrassenWith_eq_truncateColumns]
            refine matrixWidth_eq_of_first_row
              (by rw [truncateColumns_size, mulWith_size]; omega) ?_
            intro r hr
            rw [MatrixRows, truncateColumns, Array.toList_map] at hr
            rcases List.mem_map.mp hr with ⟨r', hr', rfl⟩
            have hsize' : (rowTruncateColumns
                (resOrders.map fun order ↦ order + d₁) r').size = r'.size := by
              simp [rowTruncateColumns]
            rw [hsize']
            have hr'' : r' ∈ (MatrixRows P₁).map fun r ↦
                rowMulMatrixWith lowCtx.mulContext r problem.matrix := by
              rw [← matrixRows_mulWith]
              exact hr'
            rcases List.mem_map.mp hr'' with ⟨r'', _hr'', rfl⟩
            rw [rowMulMatrixWith_size]
          have hRwidth : 0 < P₁.size →
              MatrixWidth problem.matrix ≤ MatrixWidth Rmat := by
            intro hpos
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [MatrixWidth_ofFn, ite_eq_right (by omega), hprodwidth hpos]
          constructor
          · refine rowApproximates_composed mulCtx hIH₁ hRsize hRwidth ?_ hIH₂.1
            intro l j hl hj hjw t ht
            have hd₁lt : d₁ < problem.orders.getD j 0 := by omega
            have hjres : j < resOrders.size := by
              rw [hresOrders, residualOrders]
              simpa using hj
            have hRentry : rowGet (Rmat.getD l #[]) j =
                divXTrunc d₁ (resOrders.getD j 0)
                  (rowGet ((mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                    (resOrders.map fun order ↦ order + d₁) P₁
                    problem.matrix).getD l #[]) j) := by
              rw [hRmatdef]
              simp only [residualMatrixWithProduct]
              rw [rowGet_ofFn, ite_eq_left ⟨by rw [hprodsize]; exact hl,
                by rw [hprodwidth hP₁0]; exact hjw⟩]
            rw [hRentry, divXTrunc_coeff,
              ite_eq_left (by rw [hresOrders, residualOrders,
                natArray_map_getD _ _ hj]; omega)]
            rw [mulTruncColumnStrassenWith_entry lowCtx composeLeafCutoff _ P₁
              problem.matrix (by omega) j]
            rw [truncateX_coeff, ite_eq_left (by
              rw [natArray_map_getD _ _ hjres, hresOrders, residualOrders,
                natArray_map_getD _ _ hj]
              omega)]
            rw [rowMulMatrixWith_ctx lowCtx.mulContext mulCtx]
          · rw [rowMulMatrixWith_size,
              matrixWidth_eq_of_first_row hP₁0 (fun r hr ↦ (hIH₁ r hr).2)]

omit [LawfulBEq F] in
/-- Zero rows read as zero in every coordinate. -/
private theorem pm_rowGet_eq_zero_of_rowIsZero {row : PolynomialRow F}
    (h : RowIsZero row) (j : Nat) : rowGet row j = 0 := by
  rcases Nat.lt_or_ge j row.size with hj | hj
  · rw [rowGet, array_getD_of_lt' _ _ hj]
    exact h row[j] (Array.getElem_mem_toList hj)
  · rw [rowGet, array_getD_of_le' _ _ hj]

omit [LawfulBEq F] in
/-- Rows reading as zero in every coordinate are zero rows. -/
private theorem pm_rowIsZero_of_rowGet {row : PolynomialRow F}
    (h : ∀ j, rowGet row j = 0) : RowIsZero row := by
  intro p hp
  rcases List.getElem_of_mem hp with ⟨j, hj, hget⟩
  have hj' : j < row.size := by simpa using hj
  have hzero := h j
  rw [rowGet, array_getD_of_lt' _ _ hj'] at hzero
  rw [← hget, Array.getElem_toList]
  exact hzero

/-- Spans of all-zero row sets contain only zero rows. -/
private theorem pm_rowIsZero_of_mem_rowSpan_all_zero {X : PolynomialMatrix F}
    (hall : ∀ r ∈ MatrixRows X, RowIsZero r) {row : PolynomialRow F}
    (hrow : row ∈ RowSpan X) : RowIsZero row := by
  rcases hrow with ⟨coeffs, _hsize, rfl⟩
  refine pm_rowIsZero_of_rowGet fun j ↦ ?_
  rw [pm_rowGet_rowLinearCombination]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [pm_rowGet_eq_zero_of_rowIsZero
    (hall _ (getD_mem_matrixRows (Finset.mem_range.mp hi))) j, mul_zero]

/-- Span transfer for uniform-width matrices: nonzero span members move along
any row map that covers the nonzero source rows. -/
private theorem pm_mem_rowSpan_of_nonzero_rows_mem [DecidableEq F]
    {A B : PolynomialMatrix F} {n : Nat} (hn : 0 < n)
    (hA : ∀ r ∈ MatrixRows A, r.size = n)
    (hB : ∀ r ∈ MatrixRows B, r.size = n)
    (hrows : ∀ r ∈ MatrixRows A, ¬ RowIsZero r → r ∈ RowSpan B)
    {row : PolynomialRow F} (hrow : row ∈ RowSpan A) (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan B := by
  by_cases hallzero : ∀ r ∈ MatrixRows A, RowIsZero r
  · exact absurd (pm_rowIsZero_of_mem_rowSpan_all_zero hallzero hrow) hnz
  · have hex : ∃ r ∈ MatrixRows A, ¬ RowIsZero r := by
      by_contra hnot
      refine hallzero fun r hr ↦ ?_
      by_contra hz
      exact hnot ⟨r, hr, hz⟩
    rcases hex with ⟨r₀, hr₀mem, hr₀nz⟩
    have hr₀B := hrows r₀ hr₀mem hr₀nz
    have hBpos : 0 < B.size := by
      rcases Nat.eq_zero_or_pos B.size with h0 | hp
      · exfalso
        rw [Array.eq_empty_of_size_eq_zero h0] at hr₀B
        have hr₀empty := eq_empty_of_mem_rowSpan_empty hr₀B
        have := hA r₀ hr₀mem
        rw [hr₀empty] at this
        simp at this
        omega
      · exact hp
    have hApos : 0 < A.size := size_pos_of_mem_matrixRows hr₀mem
    have hwB : MatrixWidth B = n := matrixWidth_eq_of_first_row hBpos hB
    refine rowSpan_subset_of_rows_mem (wellFormed_of_sizes hB)
      ((matrixWidth_eq_of_first_row hApos hA).trans hwB.symm) ?_ hrow
    intro r hr
    by_cases hz : RowIsZero r
    · have hreq : r = zeroRow n := by
        rw [← hA r hr]
        exact rowIsZero_eq_zeroRow hz
      rw [hreq, ← hwB]
      exact zeroRow_mem_rowSpan (wellFormed_of_sizes hB)
    · exact hrows r hr hz

/-- Nonzero rows survive zero-row compaction. -/
private theorem pm_mem_matrixRows_compactNonzeroRows {X : PolynomialMatrix F}
    {r : PolynomialRow F} (hr : r ∈ MatrixRows X) (hnz : ¬ RowIsZero r) :
    r ∈ MatrixRows (compactNonzeroRows X) := by
  rw [MatrixRows, ← Array.mem_def] at hr ⊢
  rw [compactNonzeroRows, Array.mem_filter]
  refine ⟨hr, ?_⟩
  cases hb : rowIsZero r
  · rfl
  · exact absurd (rowIsZero_iff.1 hb) hnz

/-- Zero-row compaction keeps every nonzero span member. -/
private theorem pm_mem_rowSpan_compactNonzeroRows [DecidableEq F]
    {X : PolynomialMatrix F} {n : Nat} (hn : 0 < n)
    (hsizes : ∀ r ∈ MatrixRows X, r.size = n)
    {row : PolynomialRow F} (hrow : row ∈ RowSpan X) (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan (compactNonzeroRows X) := by
  refine pm_mem_rowSpan_of_nonzero_rows_mem hn hsizes
    (fun r hr ↦ hsizes r (compactNonzeroRows_subset hr)) ?_ hrow hnz
  intro r hr hrnz
  exact matrix_row_mem_rowSpan
    (wellFormed_of_sizes fun s hs ↦ hsizes s (compactNonzeroRows_subset hs))
    (pm_mem_matrixRows_compactNonzeroRows hr hrnz)

/-- `toPoly` distinguishes canonical polynomials. -/
private theorem pm_eq_of_toPoly_eq {a b : CPolynomial F}
    (h : a.toPoly = b.toPoly) : a = b := by
  apply CPolynomial.eq_iff_coeff.2
  intro t
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, h]

/-- Column entries of a combination-by-matrix product as coefficient-weighted
sums of the row-by-matrix products. -/
private theorem pm_combination_mul_toPoly (mulCtx : CPolynomial.MulContext F)
    {P₁ M : PolynomialMatrix F} (q : PolynomialRow F) {j : Nat}
    (hj : j < MatrixWidth M) :
    (rowGet (rowMulMatrixWith mulCtx (rowLinearCombination q P₁) M) j).toPoly =
      ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
        (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) M) j).toPoly := by
  rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj]
  have hentry : ∀ k, (rowGet (rowLinearCombination q P₁) k).toPoly =
      ∑ l ∈ Finset.range P₁.size,
        (rowGet q l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly := by
    intro k
    rw [pm_rowGet_rowLinearCombination,
      pm_toPoly_finset_sum (fun l ↦ q.getD l 0 * rowGet (P₁.getD l #[]) k)
        P₁.size]
    refine Finset.sum_congr rfl fun l _hl ↦ ?_
    rw [CPolynomial.toPoly_mul]
    rfl
  calc ∑ k ∈ Finset.range M.size,
        (rowGet (rowLinearCombination q P₁) k).toPoly *
          (rowGet (M.getD k #[]) j).toPoly
      = ∑ k ∈ Finset.range M.size, ∑ l ∈ Finset.range P₁.size,
          (rowGet q l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly *
            (rowGet (M.getD k #[]) j).toPoly := by
        refine Finset.sum_congr rfl fun k _hk ↦ ?_
        rw [hentry k, Finset.sum_mul]
    _ = ∑ l ∈ Finset.range P₁.size, ∑ k ∈ Finset.range M.size,
          (rowGet q l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly *
            (rowGet (M.getD k #[]) j).toPoly := Finset.sum_comm
    _ = ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
          (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) M) j).toPoly := by
        refine Finset.sum_congr rfl fun l _hl ↦ ?_
        rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _hk ↦ ?_
        ring

/-- Converse of the composition soundness step: the coefficient row of a
full-problem solution against a lower basis solves the residual problem. -/
private theorem pm_rowApproximates_residual_of_combination
    (mulCtx : CPolynomial.MulContext F)
    {problem : XAdicProblem F} {d₁ : Nat} {P₁ Rmat : PolynomialMatrix F}
    (hP₁ : ∀ r ∈ MatrixRows P₁,
      RowApproximates mulCtx
        { orders := lowerOrders problem d₁, matrix := problem.matrix } r ∧
      r.size = problem.matrix.size)
    (hRsize : Rmat.size = P₁.size)
    (hRwidth : MatrixWidth Rmat ≤ MatrixWidth problem.matrix)
    (hR : ∀ l j, l < P₁.size → j < problem.orders.size →
      j < MatrixWidth problem.matrix →
      ∀ t, t < problem.orders.getD j 0 - d₁ →
        CPolynomial.coeff (rowGet (Rmat.getD l #[]) j) t =
          CPolynomial.coeff
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) problem.matrix) j)
            (t + d₁))
    {q : PolynomialRow F}
    (happrox : RowApproximates mulCtx problem (rowLinearCombination q P₁)) :
    RowApproximates mulCtx
      { orders := residualOrders problem d₁, matrix := Rmat } q := by
  rw [rowApproximates_iff]
  intro j hj hjw
  have hj' : j < problem.orders.size := by
    simpa [residualOrders] using hj
  have hjwM : j < MatrixWidth problem.matrix := Nat.lt_of_lt_of_le hjw hRwidth
  set o := problem.orders.getD j 0 with ho
  have horder : (residualOrders problem d₁).getD j 0 = o - d₁ := by
    rw [residualOrders, natArray_map_getD _ _ hj']
  rw [horder]
  rcases Nat.le_total o d₁ with hod | hod
  · rw [Nat.sub_eq_zero_of_le hod, pow_zero]
    exact one_dvd _
  · rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | _hP₁0
    · rw [hRsize, hP₁0, Finset.range_zero, Finset.sum_empty]
      exact dvd_zero _
    · have hP₁dvd : ∀ l, l < P₁.size →
          (Polynomial.X : Polynomial F) ^ d₁ ∣
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
              problem.matrix) j).toPoly := by
        intro l hl
        have hmem := getD_mem_matrixRows hl
        have happroxl := (hP₁ _ hmem).1 j (by simpa [lowerOrders] using hj')
        rw [truncateX_eq_zero_iff_X_pow_dvd] at happroxl
        have horderl : (lowerOrders problem d₁).getD j 0 = min o d₁ := by
          rw [lowerOrders, natArray_map_getD _ _ hj']
        rwa [horderl, Nat.min_eq_right hod] at happroxl
      have hquot : ∀ l, ∃ sl : Polynomial F, l < P₁.size →
          (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
            problem.matrix) j).toPoly = Polynomial.X ^ d₁ * sl := by
        intro l
        by_cases hl : l < P₁.size
        · rcases hP₁dvd l hl with ⟨sl, hsl⟩
          exact ⟨sl, fun _ ↦ hsl⟩
        · exact ⟨0, fun h ↦ absurd h hl⟩
      choose s hs using hquot
      have hrowdvd : (Polynomial.X : Polynomial F) ^ o ∣
          ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
              problem.matrix) j).toPoly := by
        have h0 := (rowApproximates_iff mulCtx problem _).1 happrox j hj' hjwM
        rwa [← rowGet_rowMulMatrixWith_toPoly mulCtx _ problem.matrix hjwM,
          pm_combination_mul_toPoly mulCtx q hjwM] at h0
      have hsum : ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
          (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
            problem.matrix) j).toPoly =
          Polynomial.X ^ d₁ *
            ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly * s l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [hs l (Finset.mem_range.mp hl)]
        ring
      rw [hsum, show o = d₁ + (o - d₁) from by omega, pow_add] at hrowdvd
      have hquotsum : (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
          ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly * s l :=
        (mul_dvd_mul_iff_left (pow_ne_zero d₁ Polynomial.X_ne_zero)).1 hrowdvd
      have hcong : ∀ l, l < P₁.size →
          (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
            (rowGet (Rmat.getD l #[]) j).toPoly - s l := by
        intro l hl
        rw [Polynomial.X_pow_dvd_iff]
        intro t ht
        rw [Polynomial.coeff_sub, ← CPolynomial.coeff_toPoly,
          hR l j hl hj' hjwM t (by omega), CPolynomial.coeff_toPoly]
        have hcoeff : ((rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
            problem.matrix) j).toPoly).coeff (t + d₁) =
            (Polynomial.X ^ d₁ * s l).coeff (t + d₁) := by
          rw [hs l hl]
        rw [Polynomial.coeff_X_pow_mul] at hcoeff
        rw [hcoeff]
        exact sub_self _
      have hfinal : ∑ k ∈ Finset.range Rmat.size, (rowGet q k).toPoly *
          (rowGet (Rmat.getD k #[]) j).toPoly =
          (∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly * s l) +
            ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
              ((rowGet (Rmat.getD l #[]) j).toPoly - s l) := by
        rw [hRsize, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _hl ↦ ?_
        ring
      rw [hfinal]
      exact dvd_add hquotsum
        (Finset.dvd_sum fun l hl ↦
          Dvd.dvd.mul_left (hcong l (Finset.mem_range.mp hl)) _)

/-- Combinations against a basis of combinations are combinations against the
composed product matrix. -/
private theorem pm_rowLinearCombination_combination
    (mulCtx : CPolynomial.MulContext F)
    {P₁ P₂ : PolynomialMatrix F} {n : Nat}
    (hP₁pos : 0 < P₁.size) (hP₂pos : 0 < P₂.size)
    (hsizes : ∀ r ∈ MatrixRows P₁, r.size = n)
    (w : Array (CPolynomial F)) :
    rowLinearCombination (rowLinearCombination w P₂) P₁ =
      rowLinearCombination w (mulWith mulCtx P₂ P₁) := by
  have hw₁ : MatrixWidth P₁ = n := matrixWidth_eq_of_first_row hP₁pos hsizes
  have hCsize : (mulWith mulCtx P₂ P₁).size = P₂.size := mulWith_size mulCtx P₂ P₁
  have hCsizes : ∀ r ∈ MatrixRows (mulWith mulCtx P₂ P₁), r.size = n := by
    intro r hr
    rw [matrixRows_mulWith] at hr
    rcases List.mem_map.mp hr with ⟨p₂, _hp₂, rfl⟩
    rw [rowMulMatrixWith_size, hw₁]
  have hCw : MatrixWidth (mulWith mulCtx P₂ P₁) = n :=
    matrixWidth_eq_of_first_row (by omega) hCsizes
  refine pm_row_ext ?_ fun j ↦ ?_
  · rw [pm_rowLinearCombination_size hsizes hw₁,
      pm_rowLinearCombination_size hCsizes hCw]
  · rw [pm_rowGet_rowLinearCombination, pm_rowGet_rowLinearCombination, hCsize]
    rcases Nat.lt_or_ge j n with hj | hj
    · refine pm_eq_of_toPoly_eq ?_
      rw [pm_toPoly_finset_sum
        (fun l ↦ (rowLinearCombination w P₂).getD l 0 * rowGet (P₁.getD l #[]) j)
        P₁.size]
      rw [pm_toPoly_finset_sum
        (fun i ↦ w.getD i 0 * rowGet ((mulWith mulCtx P₂ P₁).getD i #[]) j)
        P₂.size]
      have hjw₁ : j < MatrixWidth P₁ := by omega
      calc ∑ l ∈ Finset.range P₁.size,
            ((rowLinearCombination w P₂).getD l 0 *
              rowGet (P₁.getD l #[]) j).toPoly
          = ∑ l ∈ Finset.range P₁.size, ∑ i ∈ Finset.range P₂.size,
              (w.getD i 0).toPoly * (rowGet (P₂.getD i #[]) l).toPoly *
                (rowGet (P₁.getD l #[]) j).toPoly := by
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            rw [CPolynomial.toPoly_mul]
            have hwl : ((rowLinearCombination w P₂).getD l 0).toPoly =
                ∑ i ∈ Finset.range P₂.size,
                  (w.getD i 0).toPoly * (rowGet (P₂.getD i #[]) l).toPoly := by
              rw [show (rowLinearCombination w P₂).getD l 0 =
                  rowGet (rowLinearCombination w P₂) l from rfl,
                pm_rowGet_rowLinearCombination,
                pm_toPoly_finset_sum
                  (fun i ↦ w.getD i 0 * rowGet (P₂.getD i #[]) l) P₂.size]
              refine Finset.sum_congr rfl fun i _hi ↦ ?_
              rw [CPolynomial.toPoly_mul]
            rw [hwl, Finset.sum_mul]
        _ = ∑ i ∈ Finset.range P₂.size, ∑ l ∈ Finset.range P₁.size,
              (w.getD i 0).toPoly * (rowGet (P₂.getD i #[]) l).toPoly *
                (rowGet (P₁.getD l #[]) j).toPoly := Finset.sum_comm
        _ = ∑ i ∈ Finset.range P₂.size,
              (w.getD i 0 * rowGet ((mulWith mulCtx P₂ P₁).getD i #[]) j).toPoly := by
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [CPolynomial.toPoly_mul,
              mulWith_getD mulCtx P₂ P₁ (Finset.mem_range.mp hi),
              rowGet_rowMulMatrixWith_toPoly mulCtx _ P₁ hjw₁, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            ring
    · refine Eq.trans (Finset.sum_eq_zero fun l hl ↦ ?_)
        (Finset.sum_eq_zero fun i hi ↦ ?_).symm
      · have hzero : rowGet (P₁.getD l #[]) j = 0 := by
          rw [rowGet, array_getD_of_le' _ _ (by
            rw [hsizes _ (getD_mem_matrixRows (Finset.mem_range.mp hl))]
            omega)]
        rw [hzero, mul_zero]
      · have hi' : i < (mulWith mulCtx P₂ P₁).size := by
          rw [hCsize]
          exact Finset.mem_range.mp hi
        have hzero : rowGet ((mulWith mulCtx P₂ P₁).getD i #[]) j = 0 := by
          rw [rowGet, array_getD_of_le' _ _ (by
            rw [hCsizes _ (getD_mem_matrixRows hi')]
            omega)]
        rw [hzero, mul_zero]

/-- **Generation completeness of the recursive PM-basis core.**  Every nonzero
solution row of an X-adic problem lies in the row module generated by the
fuel-bounded recursive PM-basis core. -/
theorem leafRuntime_core_rowSpan_complete [DecidableEq F]
    (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F)
    (hleafRows : LeafRows mulCtx leaf) (hleafSpan : LeafSpanComplete mulCtx leaf) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      0 < problem.matrix.size → WellFormed problem.matrix →
      ∀ row : PolynomialRow F, RowApproximates mulCtx problem row →
        row.size = problem.matrix.size → ¬ RowIsZero row →
        row ∈ RowSpan (pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel problem shift) := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift hpos hwf row happrox hsize hnz
      rw [pmBasisWithFuelCore]
      exact pm_mem_rowSpan_compactNonzeroRows hpos
        (fun r hr ↦ (hleafRows problem shift r hr).2)
        (hleafSpan problem shift hpos hwf
          happrox hsize hnz)
        hnz
  | succ fuel ih =>
      intro problem shift hpos hwf row happrox hsize hnz
      rw [pmBasisWithFuelCore]
      split
      · exact pm_mem_rowSpan_compactNonzeroRows hpos
          (fun r hr ↦ (hleafRows problem shift r hr).2)
          (hleafSpan problem shift hpos hwf
            happrox hsize hnz)
          hnz
      · set d₁ := maxOrder problem / 2 with hd₁
        set lower : XAdicProblem F :=
          { orders := lowerOrders problem d₁, matrix := problem.matrix }
          with hlower
        set P₁ := pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel lower shift with hP₁def
        set resOrders := residualOrders problem d₁ with hresOrders
        set Rmat := residualMatrixWithProduct
          (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
          problem.matrix d₁ resOrders with hRmatdef
        set residual : XAdicProblem F :=
          { orders := resOrders, matrix := Rmat } with hresidual
        set shifted := updateShiftByRows P₁ shift with hshifted
        set P₂ := pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel residual shifted with hP₂def
        have hIH₁ : ∀ r ∈ MatrixRows P₁,
            RowApproximates mulCtx lower r ∧ r.size = problem.matrix.size :=
          fun r hr ↦ leafRuntime_core_rows mulCtx lowCtx leafCutoff composeLeafCutoff leaf hleafRows fuel lower shift r hr
        -- The row solves the lower-order problem.
        have hlowapprox : RowApproximates mulCtx lower row := by
          rw [rowApproximates_iff] at happrox ⊢
          intro j hj hjw
          have hj' : j < problem.orders.size := by
            simpa [hlower, lowerOrders] using hj
          refine dvd_trans (pow_dvd_pow _ ?_) (happrox j hj' hjw)
          have horder : (lowerOrders problem d₁).getD j 0 =
              min (problem.orders.getD j 0) d₁ := by
            rw [lowerOrders, natArray_map_getD _ _ hj']
          rw [hlower]
          simp only [horder]
          omega
        have hrow₁ : row ∈ RowSpan P₁ :=
          ih lower shift hpos hwf row hlowapprox hsize hnz
        rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | hP₁0
        · exfalso
          rw [Array.eq_empty_of_size_eq_zero hP₁0] at hrow₁
          have hempty := eq_empty_of_mem_rowSpan_empty hrow₁
          rw [hempty] at hsize
          simp at hsize
          omega
        · rcases hrow₁ with ⟨q, hqsize, hqeq⟩
          -- Shape facts for the residual matrix.
          have hprodsize : (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
              (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix).size =
                P₁.size := mulTruncColumnStrassenWith_size _ _ _ _ _
          have hRsize : Rmat.size = P₁.size := by
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [ofFn_size, hprodsize]
          have hprodwidth :
              MatrixWidth (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix) =
                MatrixWidth problem.matrix := by
            rw [mulTruncColumnStrassenWith_eq_truncateColumns]
            refine matrixWidth_eq_of_first_row
              (by rw [truncateColumns_size, mulWith_size]; omega) ?_
            intro r hr
            rw [MatrixRows, truncateColumns, Array.toList_map] at hr
            rcases List.mem_map.mp hr with ⟨r', hr', rfl⟩
            have hsize' : (rowTruncateColumns
                (resOrders.map fun order ↦ order + d₁) r').size = r'.size := by
              simp [rowTruncateColumns]
            rw [hsize']
            have hr'' : r' ∈ (MatrixRows P₁).map fun r ↦
                rowMulMatrixWith lowCtx.mulContext r problem.matrix := by
              rw [← matrixRows_mulWith]
              exact hr'
            rcases List.mem_map.mp hr'' with ⟨r'', _hr'', rfl⟩
            rw [rowMulMatrixWith_size]
          have hRwidth : MatrixWidth Rmat = MatrixWidth problem.matrix := by
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [MatrixWidth_ofFn, ite_eq_right (by omega), hprodwidth]
          have hRcong : ∀ l j, l < P₁.size → j < problem.orders.size →
              j < MatrixWidth problem.matrix →
              ∀ t, t < problem.orders.getD j 0 - d₁ →
                CPolynomial.coeff (rowGet (Rmat.getD l #[]) j) t =
                  CPolynomial.coeff
                    (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
                      problem.matrix) j) (t + d₁) := by
            intro l j hl hj hjw t ht
            have hd₁lt : d₁ < problem.orders.getD j 0 := by omega
            have hjres : j < resOrders.size := by
              rw [hresOrders, residualOrders]
              simpa using hj
            have hRentry : rowGet (Rmat.getD l #[]) j =
                divXTrunc d₁ (resOrders.getD j 0)
                  (rowGet ((mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                    (resOrders.map fun order ↦ order + d₁) P₁
                    problem.matrix).getD l #[]) j) := by
              rw [hRmatdef]
              simp only [residualMatrixWithProduct]
              rw [rowGet_ofFn, ite_eq_left ⟨by rw [hprodsize]; exact hl,
                by rw [hprodwidth]; exact hjw⟩]
            rw [hRentry, divXTrunc_coeff,
              ite_eq_left (by rw [hresOrders, residualOrders,
                natArray_map_getD _ _ hj]; omega)]
            rw [mulTruncColumnStrassenWith_entry lowCtx composeLeafCutoff _ P₁
              problem.matrix (by omega) j]
            rw [truncateX_coeff, ite_eq_left (by
              rw [natArray_map_getD _ _ hjres, hresOrders, residualOrders,
                natArray_map_getD _ _ hj]
              omega)]
            rw [rowMulMatrixWith_ctx lowCtx.mulContext mulCtx]
          -- The combination coefficients are nonzero and solve the residual.
          have hq_nz : ¬ RowIsZero q := by
            intro hqz
            apply hnz
            rw [hqeq]
            refine pm_rowIsZero_of_rowGet fun j ↦ ?_
            rw [pm_rowGet_rowLinearCombination]
            refine Finset.sum_eq_zero fun i _hi ↦ ?_
            rw [show q.getD i 0 = rowGet q i from rfl,
              pm_rowGet_eq_zero_of_rowIsZero hqz, zero_mul]
          have hqapprox : RowApproximates mulCtx residual q := by
            rw [hresidual, hresOrders]
            refine pm_rowApproximates_residual_of_combination mulCtx hIH₁
              hRsize (le_of_eq hRwidth) hRcong ?_
            rw [← hqeq]
            exact happrox
          have hwf_R : WellFormed Rmat := by
            refine wellFormed_of_sizes
              (n := MatrixWidth (mulTruncColumnStrassenWith lowCtx
                composeLeafCutoff (resOrders.map fun order ↦ order + d₁) P₁
                problem.matrix)) ?_
            intro r hr
            rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
            have hi' : i < Rmat.size := by simpa [MatrixRows] using hi
            have hr_eq : Rmat.getD i #[] = r := by
              rw [array_getD_of_lt' _ _ hi', ← Array.getElem_toList]
              exact hget
            rw [← hr_eq, hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [getD_ofFn, ite_eq_left (by
              rw [hRmatdef] at hi'
              simpa [residualMatrixWithProduct, ofFn_size] using hi')]
            simp
          have hRpos : 0 < Rmat.size := by omega
          have hq_size : q.size = Rmat.size := by omega
          have hrow₂ : q ∈ RowSpan P₂ :=
            ih residual shifted hRpos hwf_R q hqapprox hq_size hq_nz
          rcases hrow₂ with ⟨w, hwsize, hweq⟩
          have hP₂pos : 0 < P₂.size := by
            rcases Nat.eq_zero_or_pos P₂.size with h0 | hp
            · exfalso
              rw [Array.eq_empty_of_size_eq_zero h0] at hweq
              have hqempty : q = #[] := by
                rw [hweq, rowLinearCombination]
                rfl
              rw [hqempty] at hq_nz
              exact hq_nz rowIsZero_empty
            · exact hp
          -- Compose the two combinations through the product basis.
          have hdistrib : row =
              rowLinearCombination w (mulWith lowCtx.mulContext P₂ P₁) := by
            rw [hqeq, hweq]
            exact pm_rowLinearCombination_combination lowCtx.mulContext hP₁0
              hP₂pos (fun r hr ↦ (hIH₁ r hr).2) w
          have hfinal : row ∈ RowSpan (compactNonzeroRows
              (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁)) := by
            rw [mulStrassenWith_eq_mulWith]
            refine pm_mem_rowSpan_compactNonzeroRows hpos ?_ ?_ hnz
            · intro r hr
              rw [matrixRows_mulWith] at hr
              rcases List.mem_map.mp hr with ⟨p₂, _hp₂, rfl⟩
              rw [rowMulMatrixWith_size,
                matrixWidth_eq_of_first_row hP₁0 fun r hr ↦ (hIH₁ r hr).2]
            · exact ⟨w, by rw [mulWith_size]; omega, hdistrib⟩
          exact hfinal

/-! ## Zero padding -/

omit [BEq F] [LawfulBEq F] in
/-- Zero padding on the right does not change row reads. -/
private theorem pm_rowGet_append_replicate (row : PolynomialRow F)
    (m k : Nat) :
    rowGet (row ++ Array.replicate m (0 : CPolynomial F)) k = rowGet row k := by
  rcases Nat.lt_or_ge k row.size with hk | hk
  · rw [rowGet, rowGet, pm_append_getD_left _ hk]
  · rw [rowGet, rowGet, pm_append_getD_right _ hk, array_getD_of_le' _ _ hk]
    rcases Nat.lt_or_ge (k - row.size) m with h | h
    · rw [array_getD_of_lt' _ _ (by simpa using h), Array.getElem_replicate]
    · rw [array_getD_of_le' _ _ (by simpa using h)]

/-- Zero padding preserves the X-adic approximant conditions. -/
private theorem pm_rowApproximates_append_replicate
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    {row : PolynomialRow F} (m : Nat)
    (h : RowApproximates mulCtx problem row) :
    RowApproximates mulCtx problem
      (row ++ Array.replicate m (0 : CPolynomial F)) := by
  rw [rowApproximates_iff] at h ⊢
  intro j hj hjw
  have hsum : ∑ k ∈ Finset.range problem.matrix.size,
      (rowGet (row ++ Array.replicate m (0 : CPolynomial F)) k).toPoly *
        (rowGet (problem.matrix.getD k #[]) j).toPoly =
      ∑ k ∈ Finset.range problem.matrix.size,
        (rowGet row k).toPoly * (rowGet (problem.matrix.getD k #[]) j).toPoly :=
    Finset.sum_congr rfl fun k _hk ↦ by rw [pm_rowGet_append_replicate]
  rw [hsum]
  exact h j hj hjw

/-- Coordinates reading zero contribute no shifted entry degree. -/
private theorem pm_shiftedEntryDegree_eq_none_of_rowGet_eq_zero
    {row : PolynomialRow F} {shift : Array Nat} {j : Nat}
    (h : rowGet row j = 0) : shiftedEntryDegree? row shift j = none := by
  simp [shiftedEntryDegree?, h]

omit [LawfulBEq F] in
/-- Shifted entry degrees only depend on row reads. -/
private theorem pm_shiftedEntryDegree_congr {row row' : PolynomialRow F}
    {shift : Array Nat} {j : Nat} (h : rowGet row' j = rowGet row j) :
    shiftedEntryDegree? row' shift j = shiftedEntryDegree? row shift j := by
  simp only [shiftedEntryDegree?, h]

/-- Zero padding preserves the shifted row degree. -/
private theorem pm_rowShiftedDegree_append_replicate (row : PolynomialRow F)
    (shift : Array Nat) (m : Nat) :
    rowShiftedDegree? (row ++ Array.replicate m (0 : CPolynomial F)) shift =
      rowShiftedDegree? row shift := by
  set row' := row ++ Array.replicate m (0 : CPolynomial F) with hrow'
  have hget : ∀ j, rowGet row' j = rowGet row j :=
    pm_rowGet_append_replicate row m
  have hentry : ∀ j,
      shiftedEntryDegree? row' shift j = shiftedEntryDegree? row shift j :=
    fun j ↦ pm_shiftedEntryDegree_congr (hget j)
  have hzero_iff : RowIsZero row' ↔ RowIsZero row := by
    constructor
    · intro h
      refine pm_rowIsZero_of_rowGet fun j ↦ ?_
      rw [← hget j]
      exact pm_rowGet_eq_zero_of_rowIsZero h j
    · intro h
      refine pm_rowIsZero_of_rowGet fun j ↦ ?_
      rw [hget j]
      exact pm_rowGet_eq_zero_of_rowIsZero h j
  cases hd : rowShiftedDegree? row shift with
  | none =>
      rw [rowShiftedDegree?_eq_none_iff] at hd ⊢
      exact hzero_iff.mpr hd
  | some d =>
      cases hd' : rowShiftedDegree? row' shift with
      | none =>
          exfalso
          rw [rowShiftedDegree?_eq_none_iff] at hd'
          have hnone : rowShiftedDegree? row shift = none :=
            rowShiftedDegree?_eq_none_iff.2 (hzero_iff.mp hd')
          rw [hd] at hnone
          cases hnone
      | some d' =>
          rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hd
            with ⟨j, hj, hej⟩
          rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hd'
            with ⟨j', hj', hej'⟩
          have hj'row : j' < row.size := by
            by_contra hge
            have hzero : rowGet row j' = 0 := by
              rw [rowGet, array_getD_of_le' _ _ (by omega)]
            rw [hentry j',
              pm_shiftedEntryDegree_eq_none_of_rowGet_eq_zero hzero] at hej'
            cases hej'
          have h1 : d' ≤ d :=
            shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hd hj'row
              (by rw [← hentry j']; exact hej')
          have hsize' : row'.size = row.size + m := by
            rw [hrow']
            simp
          have h2 : d ≤ d' :=
            shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some (j := j) hd'
              (by omega) (by rw [hentry j]; exact hej)
          exact congrArg some (by omega)

/-! ## Ordered weak Popov at every level -/

/-- **The core is ordered weak Popov** on an ordered weak Popov leaf: induction over the fuel, the
composition lemma at each node (`P₂` is ordered weak Popov at `rdeg_s(P₁)`, the shift the
recursion passes it). -/
theorem leafRuntime_core_orderedWeakPopov (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F)
    (hleaf : ∀ (problem : XAdicProblem F) (shift : Array Nat),
      OrderedWeakPopov (leaf problem shift) shift problem.matrix.size) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      OrderedWeakPopov (pmBasisWithFuelCore
        (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel problem shift)
        shift problem.matrix.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift
      rw [pmBasisWithFuelCore]
      exact (hleaf problem shift).compactNonzeroRows_eq.symm ▸ hleaf problem shift
  | succ fuel ih =>
      intro problem shift
      rw [pmBasisWithFuelCore]
      split
      · exact (hleaf problem shift).compactNonzeroRows_eq.symm ▸ hleaf problem shift
      · set d₁ := maxOrder problem / 2 with hd₁
        set lower : XAdicProblem F :=
          { orders := lowerOrders problem d₁, matrix := problem.matrix } with hlower
        set P₁ := pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel lower shift
          with hP₁def
        have h₁ : OrderedWeakPopov P₁ shift problem.matrix.size := ih lower shift
        set Rmat := residualMatrixWithProduct
          (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
          problem.matrix d₁ (residualOrders problem d₁) with hRmatdef
        have hRsize : Rmat.size = problem.matrix.size := by
          rw [hRmatdef]
          simp only [residualMatrixWithProduct]
          rw [ofFn_size, mulTruncColumnStrassenWith_size, h₁.1]
        set P₂ := pmBasisWithFuelCore
          (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) fuel
          { orders := residualOrders problem d₁, matrix := Rmat }
          (updateShiftByRows P₁ shift) with hP₂def
        have h₂ : OrderedWeakPopov P₂ (updateShiftByRows P₁ shift) problem.matrix.size := by
          have := ih { orders := residualOrders problem d₁, matrix := Rmat }
            (updateShiftByRows P₁ shift)
          rwa [← hP₂def, show ({ orders := residualOrders problem d₁, matrix := Rmat } :
            XAdicProblem F).matrix.size = problem.matrix.size from hRsize] at this
        have h := orderedWeakPopov_mulWith lowCtx.mulContext h₁ h₂
        show OrderedWeakPopov
          (compactNonzeroRows (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁)) shift
          problem.matrix.size
        rw [mulStrassenWith_eq_mulWith, h.compactNonzeroRows_eq]
        exact h

/-! ## The root normalization is the identity on ordered weak Popov input -/

/-- The pivot table after the first `k` rows of an ordered weak Popov matrix: slot `i` holds
row `i` for `i < k`. -/
@[expose] def prefixTable (B : PolynomialMatrix F) (n k : Nat) :
    Array (Option (PolynomialRow F)) :=
  ((List.range n).map fun i ↦ if i < k then some (B.getD i #[]) else none).toArray

omit [BEq F] [LawfulBEq F] in
theorem prefixTable_getD (B : PolynomialMatrix F) (n k i : Nat) :
    (prefixTable B n k).getD i none = if i < n ∧ i < k then some (B.getD i #[]) else none := by
  rw [prefixTable, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [List.getElem?_range hi, Option.map_some, Option.getD_some]
    by_cases hik : i < k
    · rw [ite_eq_left hik, ite_eq_left ⟨hi, hik⟩]
    · rw [ite_eq_right hik, ite_eq_right fun h ↦ hik h.2]
  · rw [List.getElem?_eq_none (by simpa using hi), Option.map_none, Option.getD_none,
      ite_eq_right fun h ↦ absurd h.1 (by omega)]

/-- Inserting row `k` into the table of the first `k` rows puts it in its own empty slot. -/
theorem insert_prefixTable {B : PolynomialMatrix F} {s : Array Nat} {n k : Nat}
    (hB : OrderedWeakPopov B s n) (hk : k < n) (fuel : Nat) :
    insertKernelLeafPivotRowWithFuel (fuel + 1) (prefixTable B n k) s (B.getD k #[]) =
      prefixTable B n (k + 1) := by
  rcases rowShiftedLeadingTerm?_some_of_position (hB.2 k hk).2 with ⟨term, hterm, hpos⟩
  have hempty : (prefixTable B n k).getD term.position none = none := by
    rw [prefixTable_getD, hpos, ite_eq_right fun h ↦ absurd h.2 (lt_irrefl k)]
  rw [insertKernelLeafPivotRowWithFuel, hterm]
  simp only [hempty]
  apply Array.ext
  · simp [prefixTable]
  · intro i h₁ h₂
    have hi : i < n := by simpa [prefixTable] using h₂
    have e₁ := array_getD_setIfInBounds (prefixTable B n k) term.position
      (some (B.getD k #[])) i none
    have e₂ := prefixTable_getD B n (k + 1) i
    rw [array_getD_of_lt' _ _ h₁] at e₁
    rw [array_getD_of_lt' _ _ h₂] at e₂
    rw [e₁, e₂, hpos, prefixTable_getD]
    have hkn : k < (prefixTable B n k).size := by simpa [prefixTable] using hk
    by_cases hik : k = i
    · subst hik
      rw [ite_eq_left ⟨rfl, hkn⟩, ite_eq_left ⟨hi, Nat.lt_succ_self k⟩]
    · rw [ite_eq_right fun h ↦ hik h.1]
      by_cases hlt : i < k
      · rw [ite_eq_left ⟨hi, hlt⟩, ite_eq_left ⟨hi, by omega⟩]
      · rw [ite_eq_right fun h ↦ hlt h.2, ite_eq_right fun h ↦ by omega]

omit [LawfulBEq F] in
theorem orderedWeakPopov_matrixWidth {B : PolynomialMatrix F} {s : Array Nat} {n : Nat}
    (hB : OrderedWeakPopov B s n) : MatrixWidth B = n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [MatrixWidth, Array.getElem?_eq_none (by rw [hB.1]; omega), hn]
  · rw [MatrixWidth, Array.getElem?_eq_getElem (by rw [hB.1]; exact hn)]
    have := (hB.2 0 hn).1
    rwa [array_getD_of_lt' _ _ (by rw [hB.1]; exact hn)] at this

/-- **CompPoly's pivot-table reduction keeps an ordered weak Popov matrix**: every row goes to its
own empty slot (no cancellation), and the slots read back in order. -/
theorem reduceKernelLeafRows_of_orderedWeakPopov {B : PolynomialMatrix F} {s : Array Nat}
    {n : Nat} (hB : OrderedWeakPopov B s n) : reduceKernelLeafRows B s = B := by
  obtain ⟨f, hf⟩ : ∃ f, reduceKernelLeafFuel B s = f + 1 :=
    ⟨reduceKernelLeafFuel B s - 1, by
      have : 0 < reduceKernelLeafFuel B s := by
        unfold reduceKernelLeafFuel
        positivity
      omega⟩
  have hfold : ∀ k, k ≤ n →
      (B.toList.take k).foldl
        (fun pivots row ↦ insertKernelLeafPivotRowWithFuel (f + 1) pivots s row)
        (Array.replicate n none) = prefixTable B n k := by
    intro k
    induction k with
    | zero =>
        intro _
        apply Array.ext
        · simp [prefixTable]
        · intro i h₁ h₂
          simp [prefixTable]
    | succ k ih =>
        intro hk
        have hkB : k < B.toList.length := by rw [Array.length_toList, hB.1]; omega
        rw [List.take_add_one, List.getElem?_eq_getElem hkB, Option.toList_some,
          List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
        have : B.toList[k] = B.getD k #[] := by
          rw [Array.getElem_toList, array_getD_of_lt' _ _ (by rw [hB.1]; omega)]
        rw [this]
        exact insert_prefixTable hB (by omega) f
  rw [reduceKernelLeafRows, reduceKernelLeafRowsByPivots, hf, orderedWeakPopov_matrixWidth hB,
    ← Array.foldl_toList]
  have htake : B.toList.take n = B.toList := by
    rw [List.take_of_length_le (by rw [Array.length_toList, hB.1])]
  rw [← htake, hfold n le_rfl]
  apply Array.toList_inj.1
  rw [pivotRows, prefixTable, List.toList_toArray, List.toList_toArray, List.filterMap_map]
  have : (List.range n).filterMap
      (id ∘ fun i ↦ if i < n then some (B.getD i #[]) else none) =
      (List.range n).map fun i ↦ B.getD i #[] := by
    rw [List.filterMap_eq_map_iff_forall_eq_some]
    intro i hi
    rw [Function.comp_apply, id, ite_eq_left (List.mem_range.1 hi)]
  rw [this]
  apply List.ext_getElem
  · simp [hB.1]
  · intro j hj₁ hj₂
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList,
      array_getD_of_lt' _ _ (by simpa using hj₂)]

/-- No completion row is added for an ordered weak Popov matrix: every position is present. -/
theorem completeMissingPivotRows_of_orderedWeakPopov (problem : XAdicProblem F)
    {B : PolynomialMatrix F} {s : Array Nat}
    (hB : OrderedWeakPopov B s problem.matrix.size) :
    completeMissingPivotRows problem s B = B := by
  have hmiss : missingCompletionRows problem s B = #[] := by
    rw [missingCompletionRows, List.filterMap_eq_nil_iff.2]
    intro i hi
    have hi' := List.mem_range.1 hi
    have hc : rowsContainLeadingPosition B s i = true := by
      rw [rowsContainLeadingPosition]
      refine Array.any_eq_true'.2 ⟨B.getD i #[], ?_, ?_⟩
      · rw [array_getD_of_lt' _ _ (by rw [hB.1]; exact hi')]
        exact Array.getElem_mem _
      · rw [(hB.2 i hi').2]
        simp
    rw [ite_eq_left hc]
  rw [completeMissingPivotRows, hmiss, Array.append_empty]

/-- **The root normalization is the identity on ordered weak Popov input.** -/
theorem pmBasisNormalizeRoot_of_orderedWeakPopov (problem : XAdicProblem F)
    {B : PolynomialMatrix F} {s : Array Nat}
    (hB : OrderedWeakPopov B s problem.matrix.size) :
    pmBasisNormalizeRoot problem s B = B := by
  rw [pmBasisNormalizeRoot, reduceKernelLeafRows_of_orderedWeakPopov hB,
    hB.compactNonzeroRows_eq, completeMissingPivotRows_of_orderedWeakPopov problem hB]

/-- **On an ordered weak Popov leaf, the PM-basis is its core**: no root pass. -/
theorem pmBasis_leafRuntime_eq_core (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F)
    (hleaf : ∀ (problem : XAdicProblem F) (shift : Array Nat),
      OrderedWeakPopov (leaf problem shift) shift problem.matrix.size)
    (problem : XAdicProblem F) (shift : Array Nat) :
    pmBasis (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf) problem shift =
      pmBasisWithFuelCore (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf)
        (pmBasisFuel problem) problem shift := by
  rw [pmBasis, pmBasisWithFuel, pmBasisNormalizeRoot_of_orderedWeakPopov problem
    (leafRuntime_core_orderedWeakPopov mulCtx lowCtx leafCutoff composeLeafCutoff leaf hleaf
      _ problem shift)]

/-! ## The PM-basis on the leaf sorted by pivot -/

/-- The PM-basis runtime on `popovLeafBasis`. -/
@[expose] def popovRuntime (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat) :
    PMBasisRuntime F :=
  leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff popovLeafBasis

theorem popovLeafBasis_leafRows (mulCtx : CPolynomial.MulContext F) :
    LeafRows mulCtx (popovLeafBasis (F := F)) :=
  fun problem shift ↦ popovLeafBasis_rows mulCtx problem shift

theorem popovLeafBasis_leafSpanComplete [DecidableEq F] (mulCtx : CPolynomial.MulContext F) :
    LeafSpanComplete mulCtx (popovLeafBasis (F := F)) :=
  fun problem shift hpos hwf _ happrox hsize hnz ↦
    popovLeafBasis_rowSpan_complete mulCtx problem shift hpos hwf happrox hsize hnz

/-- **The PM-basis on `popovLeafBasis` is its core**, ordered weak Popov: the root pass is the
identity. -/
theorem pmBasis_popovRuntime_eq_core (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    (problem : XAdicProblem F) (shift : Array Nat) :
    pmBasis (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff) problem shift =
      pmBasisWithFuelCore (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff)
        (pmBasisFuel problem) problem shift :=
  pmBasis_leafRuntime_eq_core mulCtx lowCtx leafCutoff composeLeafCutoff popovLeafBasis
    popovLeafBasis_orderedWeakPopov problem shift

theorem popovRuntime_core_orderedWeakPopov (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat) :
    OrderedWeakPopov (pmBasisWithFuelCore
      (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff) fuel problem shift)
      shift problem.matrix.size :=
  leafRuntime_core_orderedWeakPopov mulCtx lowCtx leafCutoff composeLeafCutoff popovLeafBasis
    popovLeafBasis_orderedWeakPopov fuel problem shift

/-- Soundness: every row of the PM-basis on `popovLeafBasis` approximates the problem. -/
theorem pmBasis_popov_approximates (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    (problem : XAdicProblem F) (shift : Array Nat) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (pmBasis
      (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff) problem shift)) :
    RowApproximates mulCtx problem row := by
  rw [pmBasis_popovRuntime_eq_core] at hrow
  exact (leafRuntime_core_rows mulCtx lowCtx leafCutoff composeLeafCutoff popovLeafBasis
    (popovLeafBasis_leafRows mulCtx) _ problem shift row hrow).1

/-- **Shifted minimality of the PM-basis on `popovLeafBasis`** (CompPoly's
`pmBasis_kernelLeaf_complete_minimal`): every nonzero solution is shifted-degree dominated by a
basis row. The basis is its core, which generates every solution and is weak Popov, so the
predictable-degree property applies to it directly. -/
theorem pmBasis_popov_complete_minimal [DecidableEq F]
    (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat)
    (problem : XAdicProblem F) (shift : Array Nat) (row : PolynomialRow F)
    (hpos : 0 < problem.matrix.size) (hwf : WellFormed problem.matrix)
    (happrox : RowApproximates mulCtx problem row)
    (hnz : rowIsZero row = false) (hwidth : row.size ≤ problem.matrix.size) :
    ∃ basisRow degree,
      basisRow ∈ MatrixRows (pmBasis
        (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff) problem shift) ∧
      basisRow.size ≤ problem.matrix.size ∧
      rowShiftedDegree? basisRow shift = some degree ∧
      ∀ rowDegree, rowShiftedDegree? row shift = some rowDegree →
        degree ≤ rowDegree := by
  set n := problem.matrix.size with hn
  set row' := row ++ Array.replicate (n - row.size) (0 : CPolynomial F) with hrow'
  have hrow'size : row'.size = n := by
    rw [hrow']
    simp
    omega
  have hrownz : ¬ RowIsZero row := by
    intro h
    rw [← rowIsZero_iff, hnz] at h
    cases h
  have hrow'nz : ¬ RowIsZero row' := by
    intro h
    refine hrownz fun p hp ↦ h p ?_
    rw [hrow', Array.toList_append]
    exact List.mem_append.mpr (Or.inl hp)
  have hrow'approx : RowApproximates mulCtx problem row' :=
    pm_rowApproximates_append_replicate mulCtx problem (n - row.size) happrox
  have hrow'deg : rowShiftedDegree? row' shift = rowShiftedDegree? row shift :=
    pm_rowShiftedDegree_append_replicate row shift (n - row.size)
  set core := pmBasisWithFuelCore (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff)
    (pmBasisFuel problem) problem shift with hcore
  have hcoresizes : ∀ r ∈ MatrixRows core, r.size = n :=
    fun r hr ↦ (leafRuntime_core_rows mulCtx lowCtx leafCutoff composeLeafCutoff popovLeafBasis
      (popovLeafBasis_leafRows mulCtx) (pmBasisFuel problem) problem shift r hr).2
  have hrow'span : row' ∈ RowSpan core :=
    leafRuntime_core_rowSpan_complete mulCtx lowCtx leafCutoff composeLeafCutoff popovLeafBasis
      (popovLeafBasis_leafRows mulCtx) (popovLeafBasis_leafSpanComplete mulCtx)
      (pmBasisFuel problem) problem shift hpos hwf row' hrow'approx hrow'size hrow'nz
  have hwp : ShiftedWeakPopov core shift :=
    (popovRuntime_core_orderedWeakPopov mulCtx lowCtx leafCutoff composeLeafCutoff
      (pmBasisFuel problem) problem shift).shiftedWeakPopov
  have hdeg : rowShiftedDegree? row' shift ≠ none := by
    rw [hrow'deg]
    intro h
    exact hrownz (rowShiftedDegree?_eq_none_iff.1 h)
  obtain ⟨outRow, outDeg, rowDeg, houtmem, houtdeg, hrowdeg, hle⟩ :=
    shiftedWeakPopov_least_row_minimal core shift row'
      (wellFormed_of_sizes hcoresizes) hwp hrow'span hdeg
  refine ⟨outRow, outDeg, by rw [pmBasis_popovRuntime_eq_core]; exact houtmem,
    le_of_eq (hcoresizes outRow houtmem), houtdeg, ?_⟩
  intro rowDegree hrowDegree
  rw [hrow'deg, hrowDegree] at hrowdeg
  cases Option.some.inj hrowdeg
  exact hle

/-- The same context with the core as its basis, so no root pass runs at all: the basis is
`pmBasisWithFuelCore` at CompPoly's fuel, equal to `pmBasis` (`pmBasis_popovRuntime_eq_core`). -/
@[expose] def popovCorePMBasisContextWithLowAndCompose (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) : PMBasisContext F where
  runtime := popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff
  basis problem shift := pmBasisWithFuelCore
    (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff) (pmBasisFuel problem) problem shift
  sound := by
    intro problem shift row hrow
    rw [← pmBasis_popovRuntime_eq_core] at hrow
    exact pmBasis_popov_approximates mulCtx lowCtx leafCutoff composeLeafCutoff problem shift
      hrow
  complete_minimal := by
    let : DecidableEq F := instDecidableEqOfLawfulBEq
    intro problem shift row hpos hwf happrox hnz hwidth
    simp only [← pmBasis_popovRuntime_eq_core]
    exact pmBasis_popov_complete_minimal mulCtx lowCtx leafCutoff composeLeafCutoff problem
      shift row hpos hwf happrox hnz hwidth

end

end LeanVM.Extraction.Fast.Popov
