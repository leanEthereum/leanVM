module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Extractor.PMLane
import all CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic

/-!
# Bound: a polynomial matrix's rows over `K`

The prices of the row functions the compiled decoder shares (its PM-basis leaves and the
interpolation's least row, `Bounds/PMCore/`, `Bounds/PMSolve/`), for rows of at most `C` entries
of at most `D` coefficients (`RowWithin`) and shifts at most `S`, word-sized:

* an entry's shifted degree (a constant: its zero test reads its size, `shiftedEntryDegree?_eq`,
  `Cost/Extractor/Rewrites.lean`), a row's (`rowShiftedDegree_cost`, a fold over the row:
  `84·C + 19`), its leading position (a `find?` over the reversed indices: `168·C + 49`) and
  leading term (`rowShiftedLeadingTerm_cost`, `252·C + 3·D + 139`);
* `trimLen` and `ofArray` over `K` (`trimLen_cost`, `ofArray_cost`), `List.range'`
  (`rangeC_cost`) and a matrix's width (`matrixWidthC_cost`).

The values computed enter the prices through `limbCount` (degrees, positions) and through the
lengths iterated over: `shiftedEntryDegree?_le`, `rowShiftedDegree?_le` and
`rowShiftedLeadingTerm?_spec` bound them (the degrees by `D + S`, the position by the row's size,
the leading degree by `D`). Products of sizes are stated with `D·C` as one atom
(`affine_mul_le`), so that sums of bounds stay linear for `omega`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters
open CompPoly CompPoly.PolynomialMatrix

/-! The functions compiled on demand, by their short names (`rowGet.c438`: `Auto.…rowGet.c438`). -/
open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

/-! ## The data: rows of at most `C` entries of at most `D` coefficients -/

/-- A row of at most `C` entries, each of at most `D` coefficients. -/
@[expose] def RowWithin (C D : ℕ) (row : PolynomialRow K) : Prop :=
  row.size ≤ C ∧ ∀ e ∈ row, e.val.size ≤ D

theorem RowWithin.size_rowGet {C D : ℕ} {row : PolynomialRow K} (h : RowWithin C D row) (j : ℕ) :
    (rowGet row j).val.size ≤ D := by
  unfold rowGet
  rw [Array.getD_eq_getD_getElem?]
  cases hj : row[j]? with
  | none => exact Nat.zero_le D
  | some e => exact h.2 e (Array.mem_of_getElem? hj)

theorem RowWithin.empty (C D : ℕ) : RowWithin C D #[] := ⟨by simp, by simp⟩

theorem natDegree_le_size (p : CPolynomial K) : p.natDegree ≤ p.val.size := by
  unfold CPolynomial.natDegree
  split <;> omega

theorem size_zero_val : (↑(0 : CPolynomial K) : Array K).size = 0 := rfl

theorem toList_zero_val : (↑(0 : CPolynomial K) : Array K).toList = [] := rfl

theorem shiftedEntryDegree?_le {C D S : ℕ} {row : PolynomialRow K} (h : RowWithin C D row)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) {j v : ℕ}
    (hv : shiftedEntryDegree? row shift j = some v) : v ≤ D + S := by
  unfold shiftedEntryDegree? at hv
  by_cases hz : (rowGet row j == 0) = true
  · simp [hz] at hv
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hv
    have := natDegree_le_size (rowGet row j)
    have := h.size_rowGet j
    have := hS j
    omega

variable (P : MachineProgram)

/-! ## The shifted degree of a row -/

theorem rowGet_cost (hP : Includes P rowGet.c438.costDeps)
    (row : PolynomialRow K) (j : ℕ) :
    machineCost P rowGet.c438.costIdx [encodeValue row, encodeValue j] = 5 := by
  rw [rowGet.c438.costEq P hP]

theorem natDegree_cost (hP : Includes P Auto.CompPoly.CPolynomial.natDegree.c437.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 64) :
      machineCost P Auto.CompPoly.CPolynomial.natDegree.c437.costIdx [encodeValue p] ≤ 11 := by
  rw [Auto.CompPoly.CPolynomial.natDegree.c437.costEq P hP]
  have hp' := hp
  cases h : p.val.size with
  | zero => cost_simp; omega
  | succ k => cost_simp; omega

theorem maxOption_cost (hP : Includes P maxOption.c476.costDeps)
    (a : Option ℕ) (n : ℕ) (ha : ∀ v, a = some v → v < 2 ^ 64) (hn : n < 2 ^ 64) :
    machineCost P maxOption.c476.costIdx [encodeValue a, encodeValue n] ≤ 12 := by
  rw [maxOption.c476.costEq P hP]
  cases a with
  | none => simp
  | some v => have := ha v rfl; cost_simp; split_ifs <;> omega

/-- The fold's step of the shifted degree: an invariant of word-sized maxima. -/
theorem foldl_shiftedDegree_le {C D S : ℕ} {row : PolynomialRow K} (h : RowWithin C D row)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (l : List ℕ) (acc : Option ℕ), (∀ v, acc = some v → v ≤ D + S) →
      ∀ v, l.foldl (fun acc j ↦ match shiftedEntryDegree? row shift j with
        | none => acc
        | some d => maxOption acc d) acc = some v → v ≤ D + S := by
  intro l
  induction l with
  | nil => intro acc hacc v hv; exact hacc v hv
  | cons j l ih =>
    intro acc hacc
    apply ih
    intro v hv
    dsimp only at hv
    generalize he : shiftedEntryDegree? row shift j = o at hv
    cases o with
    | none => exact hacc v hv
    | some d =>
      have hd := shiftedEntryDegree?_le h hS he
      cases acc with
      | none => simp only [maxOption, Option.some.injEq] at hv; omega
      | some m =>
        have := hacc m rfl
        simp only [maxOption, Option.some.injEq] at hv
        omega

theorem rowShiftedDegree?_le {C D S : ℕ} {row : PolynomialRow K} (h : RowWithin C D row)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) {v : ℕ}
    (hv : rowShiftedDegree? row shift = some v) : v ≤ D + S :=
  foldl_shiftedDegree_le h hS _ none (by simp) v hv

/-- **The shifted degree of a row** (`rowShiftedDegree?`): at most `84·C + 19` (an entry's shifted
degree costs a constant: its zero test reads the entry's size, `shiftedEntryDegree?_eq`). -/
theorem rowShiftedDegree_cost
    (hP : Includes P rowShiftedDegree?.c474.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowShiftedDegree?.c474.costIdx [encodeValue row, encodeValue shift] ≤ 84 * C + 19 := by
  rw [rowShiftedDegree?.c474.costEq P hP]
  have hsz := hrow.1
  have := rangeLoop_cost P (by includes) row.size [] (by omega)
  have hfold :=
    listFoldl_le P (by includes) _ (.closure rowShiftedDegree?.c474.lam0.costIdx [encodeValue row, encodeValue shift])
    (fun acc j ↦ RunsApp.of_spec
      (rowShiftedDegree?.c474.lam0.costSpec P (by includes)
        row shift acc j))
    58 (fun acc ↦ ∀ v, acc = some v → v ≤ D + S) (List.range row.size) none
    (by simp)
    (fun acc hacc j _ ↦ by
      refine ⟨?_, ?_⟩
      · intro v hv
        generalize he : shiftedEntryDegree? row shift j = o at hv
        cases o with
        | none => exact hacc v hv
        | some d =>
          have hd := shiftedEntryDegree?_le hrow hS he
          cases acc with
          | none => simp only [maxOption, Option.some.injEq] at hv; omega
          | some m =>
            have := hacc m rfl
            simp only [maxOption, Option.some.injEq] at hv
            omega
      · rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          rowShiftedDegree?.c474.lam0.costEq P (by includes)]
        simp only [List.length_cons, List.length_nil]
        have := rowGet_cost P (by includes) row j
        have := hrow.size_rowGet j
        have := natDegree_cost P (by includes) (rowGet row j) (by omega)
        have := natDegree_le_size (rowGet row j)
        have := hS j
        generalize he : shiftedEntryDegree? row shift j = o
        cases o with
        | none => dsimp only; cost_simp; split_ifs <;> omega
        | some d =>
          have := shiftedEntryDegree?_le hrow hS he
          have := maxOption_cost P (by includes) acc d (fun v hv ↦ by have := hacc v hv; omega)
            (by omega)
          dsimp only
          cost_simp
          split_ifs <;> omega)
  simp only [List.length_range] at hfold
  cost_simp
  omega

/-! ## The shifted leading term of a row -/

/-- `List.find?` on indices: `11` per index and the predicate's price, `3` at the end. -/
theorem findNat_cost (hP : Includes P Auto.List.find?.c84.costDeps) (p : ℕ → Bool) (pVal : MachineValue)
    (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ l : List ℕ, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.find?.c84.costIdx [pVal, encodeValue l] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.find?.c84.costEq P hP p pVal hp]; simp
  | cons x l ih =>
    intro hB
    rw [Auto.List.find?.c84.costEq P hP p pVal hp]
    have h1 := ih fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    generalize p x = b
    cases b <;> dsimp only <;> nlinarith

/-- The leading position's test at one index: at most `44`. -/
theorem leadingPositionTest_cost
    (hP : Includes P rowShiftedLeadingPosition?.c486.lam0.costDeps)
    {C D S : ℕ} (hDS : D + S < 2 ^ 62) (val : ℕ) (hval : val ≤ D + S) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) (j : ℕ) :
    machineCost P rowShiftedLeadingPosition?.c486.lam0.costIdx [encodeValue val, encodeValue row, encodeValue shift, encodeValue j] ≤
      44 := by
  rw [rowShiftedLeadingPosition?.c486.lam0.costEq P hP]
  have := rowGet_cost P (by includes) row j
  have := hrow.size_rowGet j
  have := natDegree_cost P (by includes) (rowGet row j) (by omega)
  have := natDegree_le_size (rowGet row j)
  have := hS j
  generalize he : shiftedEntryDegree? row shift j = o
  cases o with
  | none => dsimp only; cost_simp; split_ifs <;> omega
  | some d =>
    have := shiftedEntryDegree?_le hrow hS he
    dsimp only
    cost_simp
    split_ifs <;> omega

/-- **The shifted leading position of a row**: at most `168·C + 49`. -/
theorem rowShiftedLeadingPosition_cost
    (hP : Includes P rowShiftedLeadingPosition?.c486.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowShiftedLeadingPosition?.c486.costIdx [encodeValue row, encodeValue shift] ≤
      168 * C + 49 := by
  rw [rowShiftedLeadingPosition?.c486.costEq P hP]
  have hsz := hrow.1
  have := rowShiftedDegree_cost P (by includes) hC hDS row hrow shift hS
  generalize he : rowShiftedDegree? row shift = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    have hval := rowShiftedDegree?_le hrow hS he
    have := rangeLoop_cost P (by includes) row.size [] (by omega)
    have := reverseAux_cost P (by includes) (List.range row.size) []
    have hf :=
      findNat_cost P (by includes) _
        (.closure rowShiftedLeadingPosition?.c486.lam0.costIdx [encodeValue val, encodeValue row, encodeValue shift])
      (fun a ↦ RunsApp.of_spec
        (rowShiftedLeadingPosition?.c486.lam0.costSpec P
          (by includes) val row shift a)) 47 (List.range row.size).reverse
      (fun a _ ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
        have := leadingPositionTest_cost P (by includes) hDS val hval row hrow shift hS a
        simp only [List.length_cons, List.length_nil]
        omega)
    simp only [List.length_reverse, List.length_range] at hf this
    dsimp only
    cost_simp
    omega

theorem rowShiftedLeadingPosition?_lt {row : PolynomialRow K} {shift : Array ℕ} {j : ℕ}
    (h : rowShiftedLeadingPosition? row shift = some j) : j < row.size := by
  unfold rowShiftedLeadingPosition? at h
  split at h
  · simp at h
  · have := List.mem_of_find?_eq_some h
    simpa using this

/-- The shifted leading term of a row of the bounds: its position in the row, its degree at
most `D`. -/
theorem rowShiftedLeadingTerm?_spec {C D : ℕ} {row : PolynomialRow K} (hrow : RowWithin C D row)
    {shift : Array ℕ} {t : ShiftedLeadingTerm K} (h : rowShiftedLeadingTerm? row shift = some t) :
    t.position < row.size ∧ t.degree ≤ D := by
  unfold rowShiftedLeadingTerm? at h
  split at h
  · rename_i j hd hj
    by_cases hz : (rowGet row j == 0) = true
    · simp [hz] at h
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      have := natDegree_le_size (rowGet row j)
      have := hrow.size_rowGet j
      exact ⟨rowShiftedLeadingPosition?_lt hj, by dsimp only; omega⟩
  · simp at h

/-- `List.beq` against the empty list: at most `7`. -/
theorem beqNilK_cost (hP : Includes P Auto.List.beq.c5.costDeps) (a : List K) :
    machineCost P Auto.List.beq.c5.costIdx [encodeValue a, encodeValue ([] : List K)] ≤ 7 := by
  cases a with
  | nil => rw [Auto.List.beq.c5.costEq_nil P hP]; simp
  | cons x a => rw [Auto.List.beq.c5.costEq_cons P hP]

/-- **The shifted leading term of a row**: at most `252·C + 3·D + 139`. -/
theorem rowShiftedLeadingTerm_cost
    (hP : Includes P rowShiftedLeadingTerm?.c535.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowShiftedLeadingTerm?.c535.costIdx [encodeValue row, encodeValue shift] ≤
      252 * C + 3 * D + 139 := by
  rw [rowShiftedLeadingTerm?.c535.costEq P hP]
  have := rowShiftedDegree_cost P (by includes) hC hDS row hrow shift hS
  have := rowShiftedLeadingPosition_cost P (by includes) hC hDS row hrow shift hS
  generalize rowShiftedDegree? row shift = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    generalize rowShiftedLeadingPosition? row shift = o'
    cases o' with
    | none => dsimp only; omega
    | some j =>
      have := rowGet_cost P (by includes) row j
      have hs := hrow.size_rowGet j
      have := beqNilK_cost P (by includes) (rowGet row j).val.toList
      have := natDegree_cost P (by includes) (rowGet row j) (by omega)
      simp only [size_zero_val, toList_zero_val] at *
      cost_simp
      split_ifs <;> omega

/-- `trimLen p n`: at most `20·n + 5`. -/
theorem trimLen_cost (hP : Includes P Auto.LeanVM.Cost.CompPolyLib.trimLen.c27.costDeps)
    (p : Array K) : ∀ n : ℕ, n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Cost.CompPolyLib.trimLen.c27.costIdx [encodeValue p, encodeValue n] ≤
        20 * n + 5 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c27.costEq P hP]; cost_simp; omega
  | succ k ih =>
    intro hk
    rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c27.costEq P hP]
    have := ih (by omega)
    cost_simp
    split_ifs <;> omega

/-- `CPolynomial.ofArray`, trimming: at most `21·|coeffs| + 14`. -/
theorem ofArray_cost (hP : Includes P Auto.CompPoly.CPolynomial.ofArray.c26.costDeps)
    (coeffs : Array K) (hs : coeffs.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.ofArray.c26.costIdx [encodeValue coeffs] ≤
      21 * coeffs.size + 14 := by
  rw [Auto.CompPoly.CPolynomial.ofArray.c26.costEq P hP]
  have := trimLen_cost P (by includes) coeffs coeffs.size hs
  have : (coeffs.extract 0 (CompPolyLib.trimLen coeffs coeffs.size)).size ≤ coeffs.size := by
    simp
  cost_simp
  omega

/-! ## Ranges and widths -/

/-- `List.range' start n`: at most `18·n + 5`. -/
theorem rangeC_cost (hP : Includes P Auto.List.range'.c86.costDeps) :
    ∀ (n start : ℕ), start + n < 2 ^ 63 →
      machineCost P Auto.List.range'.c86.costIdx [encodeValue start, encodeValue n, encodeValue 1] ≤ 18 * n + 5 := by
  intro n
  induction n with
  | zero => intro start _; rw [Auto.List.range'.c86.costEq_zero P hP]
  | succ n ih =>
    intro start h
    rw [Auto.List.range'.c86.costEq_succ P hP]
    have := ih (start + 1) (by omega)
    cost_simp
    omega

/-- The matrix's width: at most `15`. -/
theorem matrixWidthC_cost (hP : Includes P MatrixWidth.c433.costDeps) (M : PolynomialMatrix K)
    (hMs : M.size < 2 ^ 64) : machineCost P MatrixWidth.c433.costIdx [encodeValue M] ≤ 15 := by
  rw [MatrixWidth.c433.costEq P hP]
  cost_simp
  cases M[0]? <;> dsimp only <;> split_ifs <;> omega

/-- **CompPoly's `ofFn`** of an entry of price at most `B`: at most
`rows·(width·(B + 35) + 49) + 18`. -/
theorem ofFnC_cost (hP : Includes P ofFn.c441.costDeps) (rows width : ℕ) (hr : rows < 2 ^ 62)
    (hw : width < 2 ^ 62) (entry : ℕ → ℕ → CPolynomial K) (eVal : MachineValue)
    (he : ∀ a b, RunsApp P eVal [encodeValue a, encodeValue b] (encodeValue (entry a b))) (B : ℕ)
    (hB : ∀ i < rows, ∀ j < width, appCost P eVal [encodeValue i, encodeValue j] ≤ B) :
    machineCost P ofFn.c441.costIdx [encodeValue rows, encodeValue width, eVal] ≤
      rows * (width * (B + 35) + 49) + 18 := by
  rw [ofFn.c441.costEq P hP rows width entry eVal he]
  have := rangeLoop_cost P (by includes) rows [] (by omega)
  have hl := fun i ↦ RunsApp.of_spec (us := [encodeValue width, eVal]) (vs := [encodeValue i])
    (ofFn.c441.lam0.costSpec P (by includes) width entry eVal he i)
  have := map_cost P (by includes) _ (.closure ofFn.c441.lam0.costIdx [encodeValue width, eVal])
    hl (width * (B + 35) + 20) (List.range rows) (fun i hi ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [ofFn.c441.lam0.costEq P (by includes) width entry eVal he i]
      have := rangeLoop_cost P (by includes) width [] (by omega)
      have hl2 := fun j ↦ RunsApp.of_spec (us := [eVal, encodeValue i]) (vs := [encodeValue j])
        (ofFn.c441.lam0.lam0.costSpec P (by includes) entry eVal he i j)
      have := map_cost P (by includes) _ (.closure ofFn.c441.lam0.lam0.costIdx [eVal, encodeValue i])
        hl2 (B + 6) (List.range width) (fun j hj ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [ofFn.c441.lam0.lam0.costEq P (by includes) entry eVal he i j]
          have := hB i (List.mem_range.1 hi) j (List.mem_range.1 hj)
          omega)
      simp only [List.length_range, List.length_map] at *
      have e : width * (B + 35) = (B + 6 + 13) * width + 16 * width := by ring
      omega)
  simp only [List.length_range, List.length_map] at *
  have e : rows * (width * (B + 35) + 49) = (width * (B + 35) + 20 + 13) * rows + 16 * rows := by
    ring
  omega

end

end LeanVM.Cost.Bounds.Decoder
