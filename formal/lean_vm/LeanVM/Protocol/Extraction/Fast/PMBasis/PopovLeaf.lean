module

public import LeanVM.Protocol.Extraction.Fast.PMBasis.PopovCompose

/-!
# The kernel leaf, its rows sorted by pivot

CompPoly's PM-basis leaf (`kernelLeafBasis`, `KernelLeaf.lean`) reduces the scalar kernel rows and
the completion rows `X^cap·eᵢ` through a pivot table (`reduceKernelLeafRowsIncremental`), whose rows
come out with distinct shifted leading positions (`kernelLeafReduced_distinct`), and then appends a
completion row for every position no reduced row holds (`completeMissingPivotRows`): those come
last, so the leaf is not sorted by pivot.

`popovLeafBasis` fills the slots instead (`fillPivotSlots`): row `i` is the reduced row with leading
position `i`, or `X^cap·eᵢ` if there is none. It is ordered weak Popov
(**`popovLeafBasis_orderedWeakPopov`**: `n` rows, row `i` of width `n` with leading position `i`,
`n` the problem's row count), and has the same rows as CompPoly's leaf, in another order: every row
of it is a row of CompPoly's (`mem_kernelLeafBasis_of_mem_popovLeafBasis`) and every nonzero row of
CompPoly's is one of it (`mem_popovLeafBasis_of_mem_kernelLeafBasis`). So CompPoly's leaf theorems
carry over: its rows approximate the problem (**`popovLeafBasis_rows`**), and every nonzero
solution lies in its row span (**`popovLeafBasis_rowSpan_complete`**).

Credits: the leaf, the pivot-table reduction and the theorems reused here are CompPoly's
(github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors",
Valerii Huhnin).
-/

namespace LeanVM.Extraction.Fast.Popov

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open CompPoly.DenseMatrix (homogeneousKernelBasisRows array_getD_of_lt' array_getD_of_le'
  array_getD_setIfInBounds)

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Definitions -/

/-- The reduced rows of CompPoly's kernel leaf, before its completion. -/
@[expose] def kernelLeafReduced (problem : XAdicProblem F) (shift : Array Nat) :
    PolynomialMatrix F :=
  let degreeCap := leafDegreeCap problem
  let scalarRows := (homogeneousKernelBasisRows (coefficientMatrixRows problem)
      (problem.matrix.size * degreeCap)).map
    (vectorToPolynomialRow degreeCap problem.matrix.size)
  reduceKernelLeafRowsIncremental (scalarRows ++ kernelLeafCompletionRows problem) shift

/-- One insertion into the slot table: a row goes to the slot of its leading position. -/
@[expose] def slotStep (shift : Array Nat) (T : Array (Option (PolynomialRow F)))
    (row : PolynomialRow F) : Array (Option (PolynomialRow F)) :=
  match rowShiftedLeadingPosition? row shift with
  | some p => T.setIfInBounds p (some row)
  | none => T

/-- The rows' slot table: slot `p` holds a row with leading position `p` (the last one). -/
@[expose] def slotTable (n : Nat) (shift : Array Nat) (rows : PolynomialMatrix F) :
    Array (Option (PolynomialRow F)) :=
  rows.foldl (slotStep shift) (Array.replicate n none)

/-- **The filled slots**: row `i` is the row in slot `i`, or the completion row `X^cap·eᵢ`. -/
@[expose] def fillPivotSlots (problem : XAdicProblem F) (shift : Array Nat)
    (rows : PolynomialMatrix F) : PolynomialMatrix F :=
  let n := problem.matrix.size
  let T := slotTable n shift rows
  Array.ofFn fun i : Fin n ↦
    (T.getD i.val none).getD (monomialUnitRow n i.val (leafDegreeCap problem))

/-- **The leaf, sorted by pivot**: CompPoly's reduced kernel rows in their slots, completed. -/
@[expose] def popovLeafBasis (problem : XAdicProblem F) (shift : Array Nat) :
    PolynomialMatrix F :=
  fillPivotSlots problem shift (kernelLeafReduced problem shift)

/-! ## The slot table -/

omit [LawfulBEq F] in
theorem slotStep_size (shift : Array Nat) (T : Array (Option (PolynomialRow F)))
    (row : PolynomialRow F) : (slotStep shift T row).size = T.size := by
  unfold slotStep
  split <;> simp

omit [LawfulBEq F] in
/-- A slot after the fold holds what it held, or the last row of the list with that position. -/
theorem foldl_slotStep_getD (shift : Array Nat) (p : Nat) :
    ∀ (l : List (PolynomialRow F)) (T : Array (Option (PolynomialRow F))),
      (l.foldl (slotStep shift) T).getD p none = T.getD p none ∨
        ∃ b ∈ l, rowShiftedLeadingPosition? b shift = some p ∧
          (l.foldl (slotStep shift) T).getD p none = some b := by
  intro l
  induction l with
  | nil => intro T; exact Or.inl rfl
  | cons a l ih =>
      intro T
      rw [List.foldl_cons]
      rcases ih (slotStep shift T a) with h | ⟨b, hb, hbp, hget⟩
      · rw [h]
        unfold slotStep
        split
        · next q hq =>
          rw [array_getD_setIfInBounds]
          by_cases hqp : q = p ∧ q < T.size
          · rw [ite_eq_left hqp]
            exact Or.inr ⟨a, List.mem_cons_self, hqp.1 ▸ hq, rfl⟩
          · rw [ite_eq_right hqp]
            exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, hbp, hget⟩

omit [LawfulBEq F] in
/-- A filled slot stays filled. -/
theorem foldl_slotStep_ne_none (shift : Array Nat) (p : Nat) :
    ∀ (l : List (PolynomialRow F)) (T : Array (Option (PolynomialRow F))),
      T.getD p none ≠ none → (l.foldl (slotStep shift) T).getD p none ≠ none := by
  intro l
  induction l with
  | nil => intro T h; exact h
  | cons a l ih =>
      intro T h
      rw [List.foldl_cons]
      refine ih _ ?_
      unfold slotStep
      split
      · next q _ =>
        rw [array_getD_setIfInBounds]
        split
        · simp
        · exact h
      · exact h

omit [LawfulBEq F] in
/-- A row of the list with leading position `p` in range fills slot `p`. -/
theorem foldl_slotStep_filled (shift : Array Nat) {p : Nat} :
    ∀ (l : List (PolynomialRow F)) (T : Array (Option (PolynomialRow F))) (r : PolynomialRow F),
      r ∈ l → rowShiftedLeadingPosition? r shift = some p → p < T.size →
      (l.foldl (slotStep shift) T).getD p none ≠ none := by
  intro l
  induction l with
  | nil => intro T r hr; cases hr
  | cons a l ih =>
      intro T r hr hrp hpT
      rw [List.foldl_cons]
      rcases List.mem_cons.1 hr with rfl | hr
      · refine foldl_slotStep_ne_none shift p l _ ?_
        rw [slotStep, hrp, array_getD_setIfInBounds, ite_eq_left ⟨rfl, hpT⟩]
        simp
      · exact ih _ r hr hrp (by rw [slotStep_size]; exact hpT)

omit [LawfulBEq F] in
/-- What the leaf's slot table holds: rows of the list, each at its leading position. -/
theorem slotTable_getD {n : Nat} {shift : Array Nat} {rows : PolynomialMatrix F} {p : Nat}
    {r : PolynomialRow F} (h : (slotTable n shift rows).getD p none = some r) :
    r ∈ MatrixRows rows ∧ rowShiftedLeadingPosition? r shift = some p := by
  rw [slotTable, ← Array.foldl_toList] at h
  rcases foldl_slotStep_getD shift p rows.toList _ with h' | ⟨b, hb, hbp, hget⟩
  · rw [h'] at h
    rcases Nat.lt_or_ge p n with hp | hp
    · rw [array_getD_of_lt' _ _ (by simpa using hp), Array.getElem_replicate] at h
      cases h
    · rw [array_getD_of_le' _ _ (by simpa using hp)] at h
      cases h
  · rw [hget] at h
    cases h
    exact ⟨hb, hbp⟩

/-- Rows with pairwise distinct leading positions: two with the same position are equal. -/
@[expose] def DistinctPositions (rows : PolynomialMatrix F) (shift : Array Nat) : Prop :=
  ∀ a ∈ MatrixRows rows, ∀ b ∈ MatrixRows rows, ∀ p,
    rowShiftedLeadingPosition? a shift = some p →
    rowShiftedLeadingPosition? b shift = some p → a = b

omit [LawfulBEq F] in
/-- With distinct positions, every row with a position in range sits in its slot. -/
theorem slotTable_getD_of_mem {n : Nat} {shift : Array Nat} {rows : PolynomialMatrix F}
    (hd : DistinctPositions rows shift) {r : PolynomialRow F} (hr : r ∈ MatrixRows rows)
    {p : Nat} (hp : rowShiftedLeadingPosition? r shift = some p) (hpn : p < n) :
    (slotTable n shift rows).getD p none = some r := by
  have hfill := foldl_slotStep_filled shift rows.toList (Array.replicate n none) r hr hp
    (by simpa using hpn)
  have hT : slotTable n shift rows =
      rows.toList.foldl (slotStep shift) (Array.replicate n none) := by
    rw [slotTable, Array.foldl_toList]
  rw [← hT] at hfill
  cases hget : (slotTable n shift rows).getD p none with
  | none => exact absurd hget hfill
  | some b =>
      rcases slotTable_getD hget with ⟨hb, hbp⟩
      rw [hd b hb r hr p hbp hp]

/-! ## Filled slots: shape and rows -/

theorem fillPivotSlots_size (problem : XAdicProblem F) (shift : Array Nat)
    (rows : PolynomialMatrix F) : (fillPivotSlots problem shift rows).size = problem.matrix.size := by
  unfold fillPivotSlots
  simp only [Array.size_ofFn]

theorem fillPivotSlots_getD (problem : XAdicProblem F) (shift : Array Nat)
    (rows : PolynomialMatrix F) {i : Nat} (hi : i < problem.matrix.size) :
    (fillPivotSlots problem shift rows).getD i #[] =
      ((slotTable problem.matrix.size shift rows).getD i none).getD
        (monomialUnitRow problem.matrix.size i (leafDegreeCap problem)) := by
  rw [array_getD_of_lt' _ _ (by rw [fillPivotSlots_size]; exact hi)]
  unfold fillPivotSlots
  simp only [Array.getElem_ofFn]

/-- `X^d` is nonzero, of degree `d`. -/
theorem coeffXPower_one_ne_zero (d : Nat) : coeffXPower (1 : F) d ≠ 0 := by
  intro h
  have hcoeff : CPolynomial.coeff (coeffXPower (1 : F) d) d = 1 := by
    rw [CPolynomial.coeff_toPoly, coeffXPower_toPoly, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
  rw [h, CPolynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

/-- The completion row `X^d·eᵢ` has width `n` and leading position `i`. -/
theorem monomialUnitRow_leadingPosition {n i : Nat} (d : Nat) (shift : Array Nat) (hi : i < n) :
    rowShiftedLeadingPosition? (monomialUnitRow (F := F) n i d) shift = some i := by
  have hget : ∀ k, rowGet (monomialUnitRow (F := F) n i d) k ≠ 0 → k = i := by
    intro k hk
    rw [pm_rowGet_monomialUnitRow] at hk
    by_contra hki
    exact hk (ite_eq_right fun h ↦ hki h.2.symm)
  refine leadingPosition_eq_some_iff.2 ⟨?_, fun j hj ↦ ?_, fun j hij hj ↦ ?_⟩
  · rw [pm_rowGet_monomialUnitRow, ite_eq_left ⟨hi, rfl⟩]
    exact coeffXPower_one_ne_zero d
  · rw [hget j hj]
  · exact absurd (hget j hj) (by omega)

theorem monomialUnitRow_size (n i d : Nat) : (monomialUnitRow (F := F) n i d).size = n := by
  simp [monomialUnitRow]

/-- **The filled slots are ordered weak Popov**, for rows of the problem's width. -/
theorem fillPivotSlots_orderedWeakPopov (problem : XAdicProblem F) (shift : Array Nat)
    {rows : PolynomialMatrix F} (hsizes : ∀ r ∈ MatrixRows rows, r.size = problem.matrix.size) :
    OrderedWeakPopov (fillPivotSlots problem shift rows) shift problem.matrix.size := by
  refine ⟨fillPivotSlots_size _ _ _, fun i hi ↦ ?_⟩
  rw [fillPivotSlots_getD _ _ _ hi]
  cases hget : (slotTable problem.matrix.size shift rows).getD i none with
  | none =>
      exact ⟨monomialUnitRow_size _ _ _, monomialUnitRow_leadingPosition _ _ hi⟩
  | some r =>
      rcases slotTable_getD hget with ⟨hr, hrp⟩
      exact ⟨hsizes r hr, hrp⟩

/-- Every filled-slot row is a row of CompPoly's completion of the same rows. -/
theorem mem_completeMissingPivotRows_of_mem_fillPivotSlots (problem : XAdicProblem F)
    (shift : Array Nat) (rows : PolynomialMatrix F) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (fillPivotSlots problem shift rows)) :
    row ∈ MatrixRows (completeMissingPivotRows problem shift rows) := by
  rcases List.getElem_of_mem hrow with ⟨i, hi, hget⟩
  have hi' : i < problem.matrix.size := by
    simpa [MatrixRows, fillPivotSlots_size] using hi
  have hrow_eq : (fillPivotSlots problem shift rows).getD i #[] = row := by
    rw [array_getD_of_lt' _ _ (by rw [fillPivotSlots_size]; exact hi'), ← hget]
    simp [MatrixRows]
  rw [fillPivotSlots_getD _ _ _ hi'] at hrow_eq
  rw [completeMissingPivotRows, MatrixRows, Array.toList_append, List.mem_append]
  cases hslot : (slotTable problem.matrix.size shift rows).getD i none with
  | some r =>
      rw [hslot] at hrow_eq
      exact Or.inl (hrow_eq ▸ (slotTable_getD hslot).1)
  | none =>
      rw [hslot] at hrow_eq
      refine Or.inr ?_
      rw [missingCompletionRows, List.toList_toArray, List.mem_filterMap]
      refine ⟨i, List.mem_range.2 hi', ?_⟩
      have hnot : rowsContainLeadingPosition rows shift i = false := by
        rw [rowsContainLeadingPosition, Bool.eq_false_iff]
        intro hany
        rcases Array.any_eq_true'.1 hany with ⟨r, hr, hrp⟩
        cases hp : rowShiftedLeadingPosition? r shift with
        | none => rw [hp] at hrp; cases hrp
        | some p =>
            rw [hp, beq_iff_eq] at hrp
            subst hrp
            refine foldl_slotStep_filled shift rows.toList
              (Array.replicate problem.matrix.size none) r (Array.mem_def.1 hr) hp
              (by simpa using hi') ?_
            rw [Array.foldl_toList]
            exact hslot
      rw [hnot]
      exact congrArg some hrow_eq

/-- With distinct positions, every nonzero row of CompPoly's completion is a filled-slot row. -/
theorem mem_fillPivotSlots_of_mem_completeMissingPivotRows (problem : XAdicProblem F)
    (shift : Array Nat) {rows : PolynomialMatrix F}
    (hsizes : ∀ r ∈ MatrixRows rows, r.size = problem.matrix.size)
    (hd : DistinctPositions rows shift) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (completeMissingPivotRows problem shift rows))
    (hnz : ¬ RowIsZero row) :
    row ∈ MatrixRows (fillPivotSlots problem shift rows) := by
  have hmemi : ∀ i, i < problem.matrix.size →
      (fillPivotSlots problem shift rows).getD i #[] ∈
        MatrixRows (fillPivotSlots problem shift rows) := fun i hi ↦
    getD_mem_matrixRows (by rw [fillPivotSlots_size]; exact hi)
  rw [completeMissingPivotRows, MatrixRows, Array.toList_append, List.mem_append] at hrow
  rcases hrow with hr | hr
  · -- A reduced row sits in the slot of its leading position.
    have hdeg : rowShiftedDegree? row shift ≠ none :=
      fun h ↦ hnz (rowShiftedDegree?_eq_none_iff.1 h)
    rcases Option.ne_none_iff_exists'.1 hdeg with ⟨d, hd'⟩
    rcases rowShiftedLeadingPosition?_some_of_degree hd' with ⟨p, hp⟩
    have hpn : p < problem.matrix.size := hsizes row hr ▸ rowShiftedLeadingPosition?_lt hp
    have := hmemi p hpn
    rwa [fillPivotSlots_getD _ _ _ hpn, slotTable_getD_of_mem hd hr hp hpn,
      Option.getD_some] at this
  · rw [missingCompletionRows, List.toList_toArray, List.mem_filterMap] at hr
    rcases hr with ⟨i, hi, hg⟩
    have hi' := List.mem_range.1 hi
    by_cases hc : rowsContainLeadingPosition rows shift i
    · rw [ite_eq_left hc] at hg
      cases hg
    · rw [ite_eq_right hc] at hg
      cases hg
      have := hmemi i hi'
      rw [fillPivotSlots_getD _ _ _ hi'] at this
      cases hslot : (slotTable problem.matrix.size shift rows).getD i none with
      | none => rwa [hslot] at this
      | some r =>
          exfalso
          rcases slotTable_getD hslot with ⟨hr, hrp⟩
          apply hc
          rw [rowsContainLeadingPosition]
          exact Array.any_eq_true'.2 ⟨r, Array.mem_def.2 hr, by rw [hrp]; simp⟩

/-! ## The reduced rows have distinct positions -/

omit [BEq F] [LawfulBEq F] in
/-- Rows of a pivot table are stored in some slot. -/
theorem exists_slot_of_mem_pivotRows {T : Array (Option (PolynomialRow F))}
    {a : PolynomialRow F} (h : a ∈ MatrixRows (pivotRows T)) : ∃ q, T.getD q none = some a :=
  pivotRows_invariant (fun a ↦ ∃ q, T.getD q none = some a) (fun p _ h ↦ ⟨p, h⟩) h

/-- The incremental reduction keeps rows of width `n` with distinct leading positions. -/
theorem reduceKernelLeafRowsIncremental_distinct {n : Nat} (shift : Array Nat) :
    ∀ (l : List (PolynomialRow F)) (basis : PolynomialMatrix F),
      (∀ r ∈ l, r.size = n) →
      (∀ r ∈ MatrixRows basis, r.size = n) →
      let R := l.foldl (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis
      (∀ r ∈ MatrixRows R, r.size = n) ∧
        (DistinctPositions basis shift → DistinctPositions R shift) := by
  intro l
  induction l with
  | nil => intro basis _ hb; exact ⟨hb, id⟩
  | cons a l ih =>
      intro basis hl hb
      rw [List.foldl_cons]
      set T := (basis.push a).toList.foldl
        (fun pv r ↦ insertKernelLeafPivotRowWithFuel
          (reduceKernelLeafFuel (basis.push a) shift) pv shift r)
        (Array.replicate (MatrixWidth (basis.push a)) none) with hT
      have hpush : ∀ r ∈ MatrixRows (basis.push a), r.size = n := by
        intro r hr
        rw [MatrixRows, Array.toList_push, List.mem_append] at hr
        rcases hr with hr | hr
        · exact hb r hr
        · rw [List.mem_singleton.1 hr]; exact hl a List.mem_cons_self
      have hinv := insertKernelLeaf_foldl_pivotInv (n := n) (basis.push a).toList
        (reduceKernelLeafFuel (basis.push a) shift)
        (Array.replicate (MatrixWidth (basis.push a)) none) shift
        (fun r hr ↦ hpush r hr) (by
          intro p r hget
          rcases Nat.lt_or_ge p (MatrixWidth (basis.push a)) with hp | hp
          · rw [array_getD_of_lt' _ _ (by simpa using hp), Array.getElem_replicate] at hget
            cases hget
          · rw [array_getD_of_le' _ _ (by simpa using hp)] at hget
            cases hget)
      have hstep_eq : insertKernelLeafRowIncremental basis shift a =
          (pivotRows T).filter fun row ↦ !rowIsZero row := by
        rw [insertKernelLeafRowIncremental, reduceKernelLeafRows, reduceKernelLeafRowsByPivots,
          ← Array.foldl_toList]
      have hsub : ∀ r ∈ MatrixRows (insertKernelLeafRowIncremental basis shift a),
          r ∈ MatrixRows (pivotRows T) := by
        intro r hr
        rw [hstep_eq, MatrixRows, ← Array.mem_def, Array.mem_filter] at hr
        exact Array.mem_def.1 hr.1
      have hb' : ∀ r ∈ MatrixRows (insertKernelLeafRowIncremental basis shift a),
          r.size = n := by
        intro r hr
        rcases exists_slot_of_mem_pivotRows (hsub r hr) with ⟨q, hq⟩
        exact (hinv q r hq).1
      have hd' : DistinctPositions (insertKernelLeafRowIncremental basis shift a) shift := by
        intro x hx y hy p hxp hyp
        rcases exists_slot_of_mem_pivotRows (hsub x hx) with ⟨q, hq⟩
        rcases exists_slot_of_mem_pivotRows (hsub y hy) with ⟨q', hq'⟩
        have h1 := (hinv q x hq).2
        have h2 := (hinv q' y hq').2
        rw [hxp] at h1
        rw [hyp] at h2
        cases h1
        cases h2
        rw [hq] at hq'
        exact Option.some.inj hq'
      have := ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem a hr)) hb'
      exact ⟨this.1, fun _ ↦ this.2 hd'⟩

theorem vectorToPolynomialRow_size (cap width : Nat) (v : Array F) :
    (vectorToPolynomialRow cap width v).size = width := by
  simp [vectorToPolynomialRow]

/-- **CompPoly's reduced leaf rows** have the problem's width and distinct leading positions. -/
theorem kernelLeafReduced_distinct (problem : XAdicProblem F) (shift : Array Nat) :
    (∀ r ∈ MatrixRows (kernelLeafReduced problem shift), r.size = problem.matrix.size) ∧
      DistinctPositions (kernelLeafReduced problem shift) shift := by
  have h := reduceKernelLeafRowsIncremental_distinct (n := problem.matrix.size) shift
    ((((homogeneousKernelBasisRows (coefficientMatrixRows problem)
      (problem.matrix.size * leafDegreeCap problem)).map
        (vectorToPolynomialRow (leafDegreeCap problem) problem.matrix.size)) ++
      kernelLeafCompletionRows problem).toList) #[] (by
        intro r hr
        rw [Array.toList_append, List.mem_append] at hr
        rcases hr with hr | hr
        · rw [Array.toList_map, List.mem_map] at hr
          rcases hr with ⟨v, _, rfl⟩
          exact vectorToPolynomialRow_size _ _ _
        · rw [kernelLeafCompletionRows, List.toList_toArray, List.mem_map] at hr
          rcases hr with ⟨i, _, rfl⟩
          exact monomialUnitRow_size _ _ _)
      (by intro r hr; simp [MatrixRows] at hr)
  rw [kernelLeafReduced, reduceKernelLeafRowsIncremental, ← Array.foldl_toList]
  exact ⟨h.1, h.2 (by intro a ha; simp [MatrixRows] at ha)⟩

/-! ## The leaf's theorems carry over -/

/-- **The leaf is ordered weak Popov.** -/
theorem popovLeafBasis_orderedWeakPopov (problem : XAdicProblem F) (shift : Array Nat) :
    OrderedWeakPopov (popovLeafBasis problem shift) shift problem.matrix.size :=
  fillPivotSlots_orderedWeakPopov problem shift (kernelLeafReduced_distinct problem shift).1

theorem mem_kernelLeafBasis_of_mem_popovLeafBasis (problem : XAdicProblem F)
    (shift : Array Nat) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (popovLeafBasis problem shift)) :
    row ∈ MatrixRows (kernelLeafBasis problem shift) :=
  mem_completeMissingPivotRows_of_mem_fillPivotSlots problem shift _ hrow

theorem mem_popovLeafBasis_of_mem_kernelLeafBasis (problem : XAdicProblem F)
    (shift : Array Nat) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (kernelLeafBasis problem shift)) (hnz : ¬ RowIsZero row) :
    row ∈ MatrixRows (popovLeafBasis problem shift) :=
  mem_fillPivotSlots_of_mem_completeMissingPivotRows problem shift
    (kernelLeafReduced_distinct problem shift).1 (kernelLeafReduced_distinct problem shift).2
    hrow hnz

/-- **The leaf's rows approximate the problem**, at its width (CompPoly's `kernelLeafBasis_rows`). -/
theorem popovLeafBasis_rows (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    (shift : Array Nat) :
    ∀ row ∈ MatrixRows (popovLeafBasis problem shift),
      RowApproximates mulCtx problem row ∧ row.size = problem.matrix.size :=
  fun row hrow ↦ kernelLeafBasis_rows mulCtx problem shift row
    (mem_kernelLeafBasis_of_mem_popovLeafBasis problem shift hrow)

omit [BEq F] [LawfulBEq F] in
/-- Zero rows read as zero in every coordinate. -/
theorem rowGet_eq_zero_of_rowIsZero [BEq F] {row : PolynomialRow F}
    (h : RowIsZero row) (j : Nat) : rowGet row j = 0 := by
  rcases Nat.lt_or_ge j row.size with hj | hj
  · rw [rowGet, array_getD_of_lt' _ _ hj]
    exact h row[j] (Array.getElem_mem_toList hj)
  · rw [rowGet, array_getD_of_le' _ _ hj]

omit [LawfulBEq F] in
/-- A row reading zero in every coordinate is zero. -/
theorem rowIsZero_of_rowGet {row : PolynomialRow F}
    (h : ∀ j, rowGet row j = 0) : RowIsZero row := by
  intro p hp
  rcases List.getElem_of_mem hp with ⟨j, hj, rfl⟩
  have hj' : j < row.size := by simpa using hj
  have := h j
  rwa [rowGet, array_getD_of_lt' _ _ hj'] at this

/-- A span of zero rows is zero. -/
theorem rowIsZero_of_mem_rowSpan_all_zero {X : PolynomialMatrix F}
    (hall : ∀ r ∈ MatrixRows X, RowIsZero r) {row : PolynomialRow F}
    (hrow : row ∈ RowSpan X) : RowIsZero row := by
  rcases hrow with ⟨coeffs, _hsize, rfl⟩
  refine rowIsZero_of_rowGet fun j ↦ ?_
  rw [pm_rowGet_rowLinearCombination]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [rowGet_eq_zero_of_rowIsZero
    (hall _ (getD_mem_matrixRows (Finset.mem_range.mp hi))) j, mul_zero]

/-- Span transfer for uniform-width matrices: nonzero span members move along any row map
that covers the nonzero source rows (CompPoly's `pm_mem_rowSpan_of_nonzero_rows_mem`). -/
theorem mem_rowSpan_of_nonzero_rows_mem [DecidableEq F]
    {A B : PolynomialMatrix F} {n : Nat}
    (hA : ∀ r ∈ MatrixRows A, r.size = n)
    (hB : ∀ r ∈ MatrixRows B, r.size = n)
    (hrows : ∀ r ∈ MatrixRows A, ¬ RowIsZero r → r ∈ RowSpan B)
    {row : PolynomialRow F} (hrow : row ∈ RowSpan A) (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan B := by
  by_cases hallzero : ∀ r ∈ MatrixRows A, RowIsZero r
  · exact absurd (rowIsZero_of_mem_rowSpan_all_zero hallzero hrow) hnz
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
        rw [hr₀empty] at hr₀nz
        exact hr₀nz rowIsZero_empty
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

/-- **Every nonzero solution lies in the leaf's row span** (CompPoly's
`kernelLeafBasis_rowSpan_complete`). -/
theorem popovLeafBasis_rowSpan_complete [DecidableEq F]
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    (shift : Array Nat) (hpos : 0 < problem.matrix.size)
    (hwf : WellFormed problem.matrix) {row : PolynomialRow F}
    (happrox : RowApproximates mulCtx problem row)
    (hsize : row.size = problem.matrix.size)
    (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan (popovLeafBasis problem shift) := by
  have hsizesP : ∀ r ∈ MatrixRows (popovLeafBasis problem shift), r.size = problem.matrix.size :=
    fun r hr ↦ (popovLeafBasis_rows mulCtx problem shift r hr).2
  refine mem_rowSpan_of_nonzero_rows_mem
    (fun r hr ↦ (kernelLeafBasis_rows mulCtx problem shift r hr).2) hsizesP ?_
    (kernelLeafBasis_rowSpan_complete mulCtx problem shift hpos hwf happrox hsize hnz) hnz
  intro r hr hrnz
  exact matrix_row_mem_rowSpan (wellFormed_of_sizes hsizesP)
    (mem_popovLeafBasis_of_mem_kernelLeafBasis problem shift hr hrnz)

end

end LeanVM.Extraction.Fast.Popov
