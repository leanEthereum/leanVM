module

public import LeanVM.Cost.Bounds.PMCore.Glue
public import LeanVM.Cost.Bounds.Decoder.Poly
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Bounds: the leaf's row operations, compiled

The row operations of the PM-basis leaf's pivot table (CompPoly, `KernelLeaf.lean`), each on rows
of at most `C` entries of at most `D` coefficients:

* `polynomialScaleCoeffXC_cost` (`86·D + 48·d + 55`): `c·X^d·p`;
* `rowScaleCoeffXC_cost` (`(86·D + 48·d + 78)·C + 12`), `rowNegC_cost` (`(18·D + 25)·C + 8`),
  `rowAddC_cost` (`(53·D + 110)·C + 27`), `rowSubC_cost` (`(71·D + 135)·C + 39`);
* **`cancelKernelLeafLeadingTermC_cost`** (`(276·D + 717)·C + 6·D + 3214`): one cancellation
  (two leading terms, an inverse, a scaled row, a subtraction).
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable (P : MachineProgram)

/-! ## Sizes -/

theorem ofArray_size_le (a : Array K) : (CPolynomial.ofArray a).val.size ≤ a.size := by
  show (CPolynomial.Raw.trim a).size ≤ a.size
  unfold CPolynomial.Raw.trim
  split
  · simp
  · simp

theorem size_polynomialScaleCoeffX_le (c : K) (d : ℕ) (p : CPolynomial K) :
    (polynomialScaleCoeffX c d p).val.size ≤ d + p.val.size := by
  unfold polynomialScaleCoeffX
  split_ifs
  · simp [size_zero_val]
  · simp [size_zero_val]
  · have := ofArray_size_le ((List.replicate d 0 ++ p.val.toList.map fun a ↦ c * a).toArray)
    simpa using this

theorem rowWithin_rowScaleCoeffX {C D : ℕ} {row : PolynomialRow K} (h : RowWithin C D row) (c : K)
    (d : ℕ) : RowWithin C (d + D) (rowScaleCoeffX c d row) := by
  refine ⟨by simpa [rowScaleCoeffX] using h.1, fun e he ↦ ?_⟩
  simp only [rowScaleCoeffX, Array.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  have := size_polynomialScaleCoeffX_le c d p
  have := h.2 p hp
  omega

/-! ## The operations -/

/-- **`c·X^d·p`** (`polynomialScaleCoeffX`): at most `86·D + 48·d + 55`. -/
theorem polynomialScaleCoeffXC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.polynomialScaleCoeffX.c542.costDeps)
    (c : K) (d : ℕ) (p : CPolynomial K) {D : ℕ} (hp : p.val.size ≤ D) (hd : d + D < 2 ^ 62) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.polynomialScaleCoeffX.c542.costIdx
        [encodeValue c, encodeValue d, encodeValue p] ≤ 86 * D + 48 * d + 55 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.polynomialScaleCoeffX.c542.costEq P hP]
  have hb := listBeqK_cost P (by includes) p.val.toList (↑(0 : CPolynomial K) : Array K).toList
  have hr := replicate_cost P (by includes) (0 : K) d (by omega)
  have hf := fun a ↦ RunsApp.of_spec (us := [encodeValue c]) (vs := [encodeValue a])
    (Auto.CompPoly.CPolynomial.Raw.smul.c29.lam0.costSpec P (by includes) c a)
  have hm := listMap_le P Auto.List.map.c30.costIdx
    (.closure Auto.CompPoly.CPolynomial.Raw.smul.c29.lam0.costIdx [encodeValue c])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 30 p.val.toList
    (fun a _ ↦ by rw [appCost_fn, List.cons_append, List.nil_append,
      Auto.CompPoly.CPolynomial.Raw.smul.c29.lam0.costEq P (by includes)]; simp)
  have ha := append_cost P (by includes) (List.replicate d (0 : K))
    (List.map (fun a ↦ c * a) p.val.toList)
  have ho := ofArray_cost P (by includes)
    (List.replicate d (0 : K) ++ List.map (fun a ↦ c * a) p.val.toList).toArray (by simp; omega)
  simp only [Array.length_toList, size_zero_val, List.length_replicate, List.length_append,
    List.length_map, List.size_toArray] at hb hm ha ho ⊢
  split_ifs <;> omega

/-- **`c·X^d·row`** (`rowScaleCoeffX`): at most `(86·D + 48·d + 78)·C + 12`. -/
theorem rowScaleCoeffXC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.rowScaleCoeffX.c540.costDeps)
    (c : K) (d : ℕ) {C D : ℕ} (row : PolynomialRow K) (h : RowWithin C D row) (hd : d + D < 2 ^ 62) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.rowScaleCoeffX.c540.costIdx
        [encodeValue c, encodeValue d, encodeValue row] ≤ (86 * D + 48 * d + 78) * C + 12 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.rowScaleCoeffX.c540.costEq P hP]
  have hm := map_cost P (by includes) (fun p ↦ polynomialScaleCoeffX c d p)
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.rowScaleCoeffX.c540.lam0.costIdx
      [encodeValue c, encodeValue d])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.rowScaleCoeffX.c540.lam0.costSpec P (by includes)
        c d a)) (86 * D + 48 * d + 61) row.toList (fun a ha ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append, List.length_cons,
        List.length_cons, List.length_nil,
        Auto.CompPoly.PolynomialMatrix.Approximant.rowScaleCoeffX.c540.lam0.costEq P (by includes)]
      have := polynomialScaleCoeffXC_cost P (by includes) c d a (h.2 a (by simpa using ha)) hd
      omega)
  have hs := h.1
  simp only [Array.length_toList, List.length_map] at hm ⊢
  have : (86 * D + 48 * d + 61 + 13) * row.size ≤ (86 * D + 48 * d + 74) * C :=
    Nat.mul_le_mul_left _ hs
  nlinarith

theorem size_neg_val (p : CPolynomial K) : (-p).val.size = p.val.size := by
  show (CPolynomial.Raw.neg p.val).size = _
  simp [CPolynomial.Raw.neg]

theorem rowWithin_rowNeg {C D : ℕ} {row : PolynomialRow K} (h : RowWithin C D row) :
    RowWithin C D (rowNeg row) := by
  refine ⟨by simpa [rowNeg] using h.1, fun e he ↦ ?_⟩
  simp only [rowNeg, Array.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [size_neg_val]; exact h.2 p hp

/-- **`−row`** (`rowNeg`): at most `(18·D + 25)·C + 8`. -/
theorem rowNegC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowNeg.c538.costDeps)
    {C D : ℕ} (row : PolynomialRow K) (h : RowWithin C D row) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowNeg.c538.costIdx [encodeValue row] ≤
      (18 * D + 25) * C + 8 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowNeg.c538.costEq P hP]
  have hm := map_cost P (by includes) (fun p : CPolynomial K ↦ -p)
    (.closure Auto.CompPoly.PolynomialMatrix.rowNeg.c538.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.rowNeg.c538.lam0.costSpec P (by includes) a))
    (18 * D + 8) row.toList (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Auto.CompPoly.PolynomialMatrix.rowNeg.c538.lam0.costEq P
        (by includes)]
      have hf := fun x ↦ RunsApp.of_spec (us := []) (vs := [encodeValue x])
        (Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costSpec P (by includes) x)
      have hm' := listMap_le P Auto.List.map.c30.costIdx (.closure Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costIdx [])
        (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
        (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 1 a.val.toList
        (fun x _ ↦ by rw [appCost_fn, List.nil_append, List.length_nil,
          Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costEq P (by includes)])
      have := h.2 a (by simpa using ha)
      simp only [Array.length_toList, List.length_map] at hm' ⊢
      omega)
  have hs := h.1
  simp only [Array.length_toList, List.length_map] at hm ⊢
  have : (18 * D + 8 + 13) * row.size ≤ (18 * D + 21) * C := Nat.mul_le_mul_left _ hs
  nlinarith

/-- **`a + b`** (`rowAdd`): at most `(53·D + 110)·C + 27`. -/
theorem rowAddC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowAdd.c536.costDeps)
    {C D : ℕ} (hC : C < 2 ^ 62) (hD : D < 2 ^ 60) (a b : PolynomialRow K) (ha : RowWithin C D a)
    (hb : RowWithin C D b) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowAdd.c536.costIdx [encodeValue a, encodeValue b] ≤
      (53 * D + 110) * C + 27 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowAdd.c536.costEq P hP]
  have h1 := ha.1
  have h2 := hb.1
  have hr := rangeLoop_cost P (by includes) (max a.size b.size) [] (by omega)
  have hm := map_cost P (by includes) (fun j ↦ rowGet a j + rowGet b j)
    (.closure Auto.CompPoly.PolynomialMatrix.rowAdd.c536.lam0.costIdx [encodeValue a, encodeValue b])
    (fun j ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.rowAdd.c536.lam0.costSpec P (by includes) a b j))
    (53 * D + 81) (List.range (max a.size b.size)) (fun j _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append, List.length_cons,
        List.length_cons, List.length_nil,
        Auto.CompPoly.PolynomialMatrix.rowAdd.c536.lam0.costEq P (by includes),
        rowGet_cost P (by includes), rowGet_cost P (by includes)]
      have hsa := ha.size_rowGet j
      have hsb := hb.size_rowGet j
      have := addK_cost P (by includes) (rowGet a j).val (rowGet b j).val (by omega) (by omega)
      have : max (rowGet a j).val.size (rowGet b j).val.size ≤ D := by omega
      omega)
  rw [limbs_of_lt (by omega : a.size < 2 ^ 64), limbs_of_lt (by omega : b.size < 2 ^ 64)]
  simp only [List.length_range, List.length_map, max_self] at hm ⊢
  have : max a.size b.size ≤ C := by omega
  have : (53 * D + 81 + 13) * max a.size b.size ≤ (53 * D + 94) * C := Nat.mul_le_mul_left _ this
  split_ifs <;> nlinarith

/-- **`a − b`** (`rowSub`): at most `(71·D + 135)·C + 39`. -/
theorem rowSubC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowSub.c535.costDeps)
    {C D : ℕ} (hC : C < 2 ^ 62) (hD : D < 2 ^ 60) (a b : PolynomialRow K) (ha : RowWithin C D a)
    (hb : RowWithin C D b) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowSub.c535.costIdx [encodeValue a, encodeValue b] ≤
      (71 * D + 135) * C + 39 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowSub.c535.costEq P hP]
  have := rowNegC_cost P (by includes) b hb
  have := rowAddC_cost P (by includes) hC hD a (rowNeg b) ha (rowWithin_rowNeg hb)
  nlinarith

theorem rowWithin_mono {C D D' : ℕ} {row : PolynomialRow K} (h : RowWithin C D row) (hD : D ≤ D') :
    RowWithin C D' row :=
  ⟨h.1, fun e he ↦ (h.2 e he).trans hD⟩

/-- **One cancellation** (`cancelKernelLeafLeadingTerm`): at most
`(276·D + 717)·C + 6·D + 3214`. -/
theorem cancelKernelLeafLeadingTermC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.cancelKernelLeafLeadingTerm.c534.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 60) (hD : D < 2 ^ 58) (hDS : 2 * D + S < 2 ^ 61)
    (target reducer : PolynomialRow K) (ht : RowWithin C D target) (hr : RowWithin C D reducer)
    (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.cancelKernelLeafLeadingTerm.c534.costIdx
        [encodeValue target, encodeValue reducer, encodeValue shift] ≤
      (276 * D + 717) * C + 6 * D + 3214 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.cancelKernelLeafLeadingTerm.c534.costEq P hP]
  have h1 := rowShiftedLeadingTerm_cost P (by includes) (by omega) (by omega) target ht shift hS
  have h2 := rowShiftedLeadingTerm_cost P (by includes) (by omega) (by omega) reducer hr shift hS
  have h3 : 717 * C ≤ (276 * D + 717) * C := Nat.mul_le_mul_right _ (by omega)
  generalize htt : rowShiftedLeadingTerm? target shift = o
  cases o with
  | none => dsimp only; omega
  | some t =>
    generalize hrt : rowShiftedLeadingTerm? reducer shift = o'
    cases o' with
    | none => dsimp only; omega
    | some r =>
      obtain ⟨htp, htd⟩ := rowShiftedLeadingTerm?_spec ht htt
      obtain ⟨hrp, hrd⟩ := rowShiftedLeadingTerm?_spec hr hrt
      have := ht.1
      have := hr.1
      have := invK_cost P (by includes) r.coeff
      have hsc := rowScaleCoeffXC_cost P (by includes) (t.coeff / r.coeff) (t.degree - r.degree)
        reducer hr (by omega)
      have hsub := rowSubC_cost P (by includes) (C := C) (D := 2 * D) (by omega) (by omega) target
        (rowScaleCoeffX (t.coeff / r.coeff) (t.degree - r.degree) reducer) (rowWithin_mono ht (by omega))
        (rowWithin_mono (rowWithin_rowScaleCoeffX hr _ _) (by omega))
      have e1 : (86 * D + 48 * (t.degree - r.degree) + 78) * C ≤ (134 * D + 78) * C :=
        Nat.mul_le_mul_right _ (by omega)
      have e2 : (71 * (2 * D) + 135) * C = (142 * D + 135) * C := by ring
      have e3 : (276 * D + 717) * C = (134 * D + 78) * C + (142 * D + 135) * C + 504 * C := by ring
      dsimp only
      rw [limbs_of_lt (by omega : t.position < 2 ^ 64), limbs_of_lt (by omega : r.position < 2 ^ 64),
        limbs_of_lt (by omega : t.degree < 2 ^ 64), limbs_of_lt (by omega : r.degree < 2 ^ 64)]
      simp only [max_self]
      split_ifs <;> omega

end

end LeanVM.Cost.Bounds.PMCore
