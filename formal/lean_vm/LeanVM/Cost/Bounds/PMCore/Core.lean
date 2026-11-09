module

public import LeanVM.Cost.Bounds.PMCore.Glue
public import LeanVM.Cost.Bounds.PMCore.Products
public import LeanVM.Cost.Bounds.PMFFT.EvalCost
public import LeanVM.Cost.Bounds.PMBasis.Recursion
public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeRecursion
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.XAdicSoundness
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Bounds: the PM-basis core, compiled

`pmCoreC` (`Cost/Extractor/PMCore.lean`) is CompPoly's `pmBasisWithFuelCore` on the target
runtime `popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1` (the ordered-weak-Popov
leaf at order one, the evaluation-domain products). Its price, by its two equations
(`pmCoreC.costEq_zero`, `pmCoreC.costEq_succ`) through the model's recursion
(`pmBasisWithFuelCore_price_le`, `Bounds/PMBasis/Recursion.lean`):

* **`residualMatrixC_cost`**: the residual `(P₁·A) div X^d`: the column-truncated product
  (`mulTruncEvalPC_cost`) and `R·W` entries of at most `58·O + 89` each;
* **`pmCoreC_node`**: a node's own price at maximal order `o` is at most
  `pmNodePrice p r m o` (`FFTPricesOK p`), the products within `evalMatPrice` , the sizes from
  `popovRuntime_core_node` (exactly `r` rows, degrees at most the halves' orders);
* **`pmCoreC_cost`**: on a problem of `r ≥ m` rows of width `m` (`CoreInv`: shifts plus twice the
  maximal order at most `SB < 2^60`), at the fuel `pmBasisFuel = maxOrder + 1`, the price is at
  most `pmTree 1 L (pmNodePrice p r m) (maxOrder problem)`, `L` the leaf's price (`LeafCost`: the
  ordered-weak-Popov leaf and its compaction within `Lc`) and `21·m + 32`.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder LeanVM.Cost.Bounds.PMBasis
open LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT
open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

/-! ## The products' shapes -/

theorem rowWithin_empty (C D : ℕ) : RowWithin C D (#[] : PolynomialRow K) :=
  ⟨by simp, by simp⟩

theorem mulTruncEvalP_size (ords : Array ℕ) (A B : PolynomialMatrix K) :
    (mulTruncEvalP novelTransform fftMulContext ords A B).size = A.size := by
  rw [mulTruncEvalP_eq, EvalMat.mulTruncEval_eq_truncateColumns _ _ fftMulContext,
    truncateColumns_size, mulWith_size]

theorem mulTruncEvalP_width_le (ords : Array ℕ) (A B : PolynomialMatrix K) :
    MatrixWidth (mulTruncEvalP novelTransform fftMulContext ords A B) ≤ MatrixWidth B := by
  rw [mulTruncEvalP_eq, EvalMat.mulTruncEval_eq_truncateColumns _ _ fftMulContext,
    PMDegree.matrixWidth_eq_getD_size']
  rcases Nat.eq_zero_or_pos A.size with h0 | hpos
  · have : (truncateColumns ords (mulWith fftMulContext A B)).size = 0 := by
      rw [truncateColumns_size, mulWith_size, h0]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp
  · rw [truncateColumns_getD _ _ (by rw [mulWith_size]; exact hpos), mulWith_getD _ _ _ hpos]
    simp [rowTruncateColumns, rowMulMatrixWith_size]

/-- The naive product `A·B`: `|A|` rows of at most `width B` entries of at most `dA + dB + 1`
coefficients. -/
theorem mulWith_shape (ctx : CPolynomial.MulContext K) (A B : PolynomialMatrix K) {dA dB : ℕ}
    (hA : DegLe A dA) (hB : DegLe B dB) :
    (mulWith ctx A B).size = A.size ∧
      ∀ i, RowWithin (MatrixWidth B) (dA + dB + 1) ((mulWith ctx A B).getD i #[]) := by
  refine ⟨mulWith_size _ _ _, fun i ↦ ?_⟩
  rcases Nat.lt_or_ge i A.size with hi | hi
  · rw [mulWith_getD _ _ _ hi]
    refine ⟨by rw [rowMulMatrixWith_size], fun e he ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
    have hd := PMDegree.natDegree_rowGet_rowMulMatrixWith_le ctx (A.getD i #[]) B
      (a := dA) (b := dB) (fun k ↦ hA i k) (fun r hr j ↦ by
        rw [MatrixRows] at hr
        obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hr
        have e : B.toList[l] = B.getD l #[] := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hl)]; simp
        rw [e]; exact hB l j) j
    have hrg : rowGet (rowMulMatrixWith ctx (A.getD i #[]) B) j =
        (rowMulMatrixWith ctx (A.getD i #[]) B)[j] := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; rfl
    rw [hrg] at hd
    have := PMDegree.val_size_le_natDegree_add_one (rowMulMatrixWith ctx (A.getD i #[]) B)[j]
    omega
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [mulWith_size]; omega)]
    exact rowWithin_empty _ _

theorem degLe_of_rows {M : PolynomialMatrix K} {d : ℕ}
    (h : ∀ r ∈ MatrixRows M, ∀ j, (rowGet r j).natDegree ≤ d) : DegLe M d := by
  intro i j
  rcases Nat.lt_or_ge i M.size with hi | hi
  · exact h _ (getD_mem_matrixRows hi) j
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp only [Option.getD_none, rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_empty]
    rw [CPolynomial.natDegree_zero]
    exact Nat.zero_le _

theorem matrixWidth_of_rows {M : PolynomialMatrix K} {r m : ℕ} (hs : M.size = r) (hr : 1 ≤ r)
    (h : ∀ row ∈ M.toList, row.size = m) : MatrixWidth M = m := by
  rw [PMDegree.matrixWidth_eq_getD_size']
  exact h _ (by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]; simp)

/-! ## The residual matrix -/

variable (P : MachineProgram)

/-- **The residual** `(P₁·A) div X^d` truncated at `orders` (`residualMatrixC`): the
column-truncated product, then `|P₁|·width` entries, each at most `58·O + 89` (`O` the residual
orders' bound). -/
theorem residualMatrixC_cost (hP : Includes P residualMatrixC.costDeps)
    (basis matrix : PolynomialMatrix K) (d : ℕ) (orders : Array ℕ) {O : ℕ}
    (hO : ∀ j, orders.getD j 0 ≤ O) (hdO : d + O < 2 ^ 62)
    (hbs : basis.size < 2 ^ 62) (hmw : MatrixWidth matrix < 2 ^ 62) :
    machineCost P residualMatrixC.costIdx
        [encodeValue basis, encodeValue matrix, encodeValue d, encodeValue orders] ≤
      21 * orders.size + 59 +
        machineCost P mulTruncEvalPC.costIdx [encodeValue (orders.map fun order ↦ order + d),
          encodeValue basis, encodeValue matrix] +
        basis.size * ((58 * O + 89) * MatrixWidth matrix + 49) := by
  rw [residualMatrixC.costEq P hP]
  have hord : ∀ x ∈ orders, x ≤ O := fun x hx ↦ by
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
    have := hO j
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at this
  have hm := map_cost P (by includes) (fun order : ℕ ↦ order + d)
    (.closure residualMatrixC.lam0.costIdx [encodeValue d])
    (fun a ↦ RunsApp.of_spec (residualMatrixC.lam0.costSpec P (by includes) d a)) 4
    orders.toList (fun a ha ↦ by
      have := hord a (by simpa using ha)
      rw [appCost_fn, List.singleton_append, residualMatrixC.lam0.costEq P (by includes)]
      cost_simp
      omega)
  set prod := mulTruncEvalP novelTransform fftMulContext (orders.map fun order ↦ order + d)
    basis matrix with hprod
  have hps : prod.size = basis.size := mulTruncEvalP_size _ _ _
  have hpw : MatrixWidth prod ≤ MatrixWidth matrix := mulTruncEvalP_width_le _ _ _
  have hw := matrixWidthC_cost P (by includes) prod (by omega)
  have hf := fun a b ↦ RunsApp.of_spec (us := [encodeValue d, encodeValue orders, encodeValue prod])
    (vs := [encodeValue a, encodeValue b]) (residualMatrixC.lam1.costSpec P (by includes) d orders prod a b)
  have hof := ofFnC_cost P (by includes) prod.size (MatrixWidth prod) (by omega) (by omega) _
    (.closure residualMatrixC.lam1.costIdx [encodeValue d, encodeValue orders, encodeValue prod])
    hf (58 * O + 54) (fun i _ j _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [residualMatrixC.lam1.costEq P (by includes), rowGet_cost P (by includes)]
      have := divXTruncC_cost P (by includes) d (orders.getD j 0)
        (rowGet (prod.getD i #[]) j) (by have := hO j; omega)
      have := hO j
      omega)
  have hof2 : prod.size * (MatrixWidth prod * (58 * O + 54 + 35) + 49) ≤
      prod.size * ((58 * O + 54 + 35) * MatrixWidth prod + 49) :=
    Nat.mul_le_mul_left _ (by rw [Nat.mul_comm (MatrixWidth prod)])
  have h1 : (58 * O + 54 + 35) * MatrixWidth prod ≤ (58 * O + 89) * MatrixWidth matrix :=
    Nat.mul_le_mul_left _ hpw
  have h2 : prod.size * ((58 * O + 54 + 35) * MatrixWidth prod + 49) ≤
      basis.size * ((58 * O + 89) * MatrixWidth matrix + 49) := by
    rw [hps]; exact Nat.mul_le_mul_left _ (by omega)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega


/-! ## The recursion on the target runtime -/

/-- The target runtime: the ordered-weak-Popov PM-basis on evaluation-domain products, cutoff `1`. -/
abbrev targetRT : PMBasisRuntime K := popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1

/-- **The invariant** of the problems the recursion visits: `r` rows of width `m`, at most `m`
orders, word-sized entries, the shifts plus twice the maximal order at most `SB`, the maximal
order at most `2^37/3` (every transform of at most `2^36` points). -/
@[expose] def CoreInv (r m SB : ℕ) (problem : XAdicProblem K) (shift : Array ℕ) : Prop :=
  problem.matrix.size = r ∧ (∀ row ∈ problem.matrix.toList, row.size = m) ∧
    problem.orders.size ≤ m ∧ SizeLe problem.matrix (2 ^ 40) ∧
    (∀ j, shift.getD j 0 + 2 * maxOrder problem ≤ SB) ∧ 3 * maxOrder problem ≤ 2 ^ 37

/-- **The leaf's price**: the ordered-weak-Popov leaf at order at most one and its compaction,
within `Lc`, on the invariant's problems. -/
@[expose] def LeafCost (P : MachineProgram) (r m SB Lc : ℕ) : Prop :=
  ∀ problem shift, CoreInv r m SB problem shift → maxOrder problem ≤ 1 →
    machineCost P popovLeafC.costIdx [encodeValue problem, encodeValue shift] +
      machineCost P compactNonzeroRowsC.costIdx [encodeValue (Popov.popovLeafBasis problem shift)] ≤
        Lc

theorem rowWithin_of_rows {M : PolynomialMatrix K} {C D : ℕ}
    (hsz : ∀ row ∈ M.toList, row.size ≤ C) (hD : SizeLe M D) (i : ℕ) : RowWithin C D (M.getD i #[]) := by
  rcases Nat.lt_or_ge i M.size with hi | hi
  · have hmem : M.getD i #[] ∈ M.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]; simp
    refine ⟨hsz _ hmem, fun e he ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
    have := hD i j
    rwa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at this
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact rowWithin_empty _ _

/-- The updated shift: at most `X` where every row's shifted degree and every shift is. -/
theorem updateShiftByRows_getD_le (B : PolynomialMatrix K) (shift : Array ℕ) {X : ℕ}
    (hrow : ∀ i v, rowShiftedDegree? (B.getD i #[]) shift = some v → v ≤ X)
    (hs : ∀ j, shift.getD j 0 ≤ X) (j : ℕ) : (updateShiftByRows B shift).getD j 0 ≤ X := by
  unfold updateShiftByRows
  rw [Array.getD_eq_getD_getElem?]
  rcases Nat.lt_or_ge j B.size with hj | hj
  · rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj]
    simp only [Option.map_some, Option.getD_some]
    cases hv : rowShiftedDegree? (B.getD j #[]) shift with
    | none => exact hs j
    | some v => exact hrow j v hv
  · rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_none (by simp; omega)]
    simp

/-- The node's glue and the residual product's truncations within the overhead term. -/
theorem glue_le (r m o ovh d : ℕ) (hr : 2 ≤ r) (ho : 2 ≤ o) (hovh : 80 ≤ ovh)
    (hd : 2 * (o - d) ≤ o + 1) :
    r * ((58 * (o - d) + 89) * m + 49) + (84 * r + 63) * r + ((3 * (o + 1) + 33) * r + 30) * r +
        88 * m + ovh * ((r * r + r * m + r * m) * (o + 1)) ≤
      ovh * (r * (2 * r + 4 * m) * (o + 1)) := by
  generalize he : o - d = e at hd
  have h59 : 58 * e ≤ 29 * (o + 1) := by omega
  have hA : r * ((58 * e + 89) * m + 49) ≤ r * m * (29 * (o + 1)) + 89 * (r * m) + 49 * r := by
    have := Nat.mul_le_mul_right m h59
    nlinarith
  have hsplit : ovh * (r * (2 * r + 4 * m) * (o + 1)) =
      ovh * ((r * r + r * m + r * m) * (o + 1)) + ovh * ((r * r + 2 * (r * m)) * (o + 1)) := by
    ring
  have hB : 80 * ((r * r + 2 * (r * m)) * (o + 1)) ≤ ovh * ((r * r + 2 * (r * m)) * (o + 1)) :=
    Nat.mul_le_mul_right _ hovh
  have hrm : m ≤ r * m := Nat.le_mul_of_pos_left m (by omega)
  have hrr : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have ho1 : 3 ≤ o + 1 := by omega
  have hX : 3 * (r * m) ≤ r * m * (o + 1) := by nlinarith
  have hY : 3 * (r * r) ≤ r * r * (o + 1) := by nlinarith
  nlinarith

theorem targetRT_eq' : popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1 =
    Popov.popovRuntime fftMulContext fftMulLowContext 1 1 :=
  popovEvalRuntime_eq _ _ _ 1 1

theorem popovRuntime_leafCutoff :
    (Popov.popovRuntime fftMulContext fftMulLowContext 1 1).leafCutoff = 1 := rfl

/-- **A node of the compiled core**: at maximal order `o ≥ 2` (fuel at least `o − 1`), its price
is at most `pmNodePrice p r m o` and its two children's. -/
theorem pmCoreC_node (hP : Includes P pmCoreC.costDeps) {p : PMPrices} (hp : PMFFT.FFTPricesOK p)
    {r m SB : ℕ} (hr : 2 ≤ r) (hm : m ≤ r)
    (hr30 : r < 2 ^ 30) (hSB : SB < 2 ^ 39) (problem : XAdicProblem K) (shift : Array ℕ)
    (hI : CoreInv r m SB problem shift) (n : ℕ) (hn : n + 1 < 2 ^ 62)
    (hge : 2 ≤ maxOrder problem) (hfuel : maxOrder problem ≤ n + 2) :
    machineCost P pmCoreC.costIdx [encodeValue (n + 1), encodeValue problem, encodeValue shift] ≤
      pmNodePrice p r m (maxOrder problem) +
        machineCost P pmCoreC.costIdx [encodeValue n, encodeValue (pmLower problem), encodeValue shift] +
        machineCost P pmCoreC.costIdx [encodeValue n, encodeValue (pmResidual targetRT n problem shift),
          encodeValue (pmShifted targetRT n problem shift)] := by
  obtain ⟨hIs, hIrows, hIord, hIsz, hIsh, hI3⟩ := hI
  have hh := PMDegree.popovRuntime_core_node fftMulContext fftMulLowContext 1 (le_refl _) n problem
    shift hge hfuel
  dsimp only at hh
  obtain ⟨-, hd1, hd2, -, -, -, -, hP1s, hP1r, hRs, hRr, hRe, hP2s, hP2r⟩ := hh
  rw [pmCoreC.costEq_succ P hP]
  unfold pmNodePrice
  simp only [pmLower, pmResidual, pmShifted, targetRT]
  rw [targetRT_eq', popovRuntime_leafCutoff]
  have hd : decide (maxOrder problem ≤ 1) = false := by simp; omega
  simp only [hd, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  set o := maxOrder problem with ho
  set d := o / 2 with hdd
  set RT := Popov.popovRuntime fftMulContext fftMulLowContext 1 1 with hRT
  set P₁ := pmBasisWithFuelCore RT n { orders := lowerOrders problem d, matrix := problem.matrix }
    shift with hP₁
  set R := residualMatrixWithProduct RT.residualProduct P₁
    problem.matrix d (residualOrders problem d) with hR
  set P₂ := pmBasisWithFuelCore RT n { orders := residualOrders problem d, matrix := R }
    (updateShiftByRows P₁ shift) with hP₂
  have hord : ∀ x ∈ problem.orders, x ≤ o := le_maxOrder problem
  have ho38 : o < 2 ^ 38 := by have := hIsh 0; omega
  have hmw : MatrixWidth problem.matrix = m := matrixWidth_of_rows hIs (by omega) hIrows
  rw [hIs] at hP1s hP1r
  have hP1D : DegLe P₁ d := degLe_of_rows fun row hrow j ↦ (hP1r row hrow).2 j
  have hP2r' : ∀ row ∈ MatrixRows P₂, row.size = problem.matrix.size ∧
      ∀ j, (rowGet row j).natDegree ≤ o - d := hP2r
  have hP2D : DegLe P₂ (o - d) := degLe_of_rows fun row hrow j ↦ (hP2r' row hrow).2 j
  have hP1w : MatrixWidth P₁ = r := matrixWidth_of_rows hP1s (by omega) fun row hrow ↦
    (hP1r row hrow).1
  have hP2s' : P₂.size = r := (hP2s : P₂.size = problem.matrix.size).trans hIs
  -- the glue
  have hMO := maxOrderC_cost P (by includes) problem (fun x hx ↦ by have := hord x hx; omega)
  have hLO := lowerOrdersC_cost P (by includes) problem d (by omega)
    (fun x hx ↦ by have := hord x hx; omega)
  have hRO := residualOrdersC_cost P (by includes) problem d (by omega)
    (fun x hx ↦ by have := hord x hx; omega)
  have hRO' : ∀ j, (residualOrders problem d).getD j 0 ≤ o - d := fun j ↦ getD_le_of_mem
    fun x hx ↦ by
      simp only [residualOrders, Array.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hord y hy; omega
  have hRM := residualMatrixC_cost P (by includes) P₁ problem.matrix d (residualOrders problem d)
    hRO' (by omega) (by omega) (by omega)
  have hBD : DegLe problem.matrix (2 ^ 40 - 1) := fun i j ↦ by
    have := natDegree_le_size_sub_one' (rowGet (problem.matrix.getD i #[]) j)
    have := hIsz i j
    omega
  have hP1pos : 0 < P₁.size := by omega
  have hMTb := PMFFT.mulTruncEvalPC_cost P (by includes) p hp
    ((residualOrders problem d).map fun order ↦ order + d) P₁ problem.matrix d (2 ^ 40 - 1) o hP1D hBD
    (fun c ↦ getD_le_of_mem fun x hx ↦ by
      simp only [residualOrders, Array.mem_map] at hx
      obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
      have := hord z hz; omega) (by omega) (by omega) (by omega)
    (by
      rw [Nat.min_eq_left (by omega : d ≤ o - 1), Nat.min_eq_right (by omega : o - 1 ≤ 2 ^ 40 - 1)]
      exact clog2_le (by omega))
    hP1pos (by omega) (by omega) (by omega) (by omega)
  rw [Nat.min_eq_left (by omega : d ≤ o - 1), Nat.min_eq_right (by omega : o - 1 ≤ 2 ^ 40 - 1)]
    at hMTb
  have hUS := updateShiftByRowsC_cost P (by includes) (C := r) (D := d + 1) (S := SB) (by omega)
    (by omega) P₁ (by omega) (fun i ↦ by
      rcases Nat.lt_or_ge i P₁.size with hi | hi
      · have hmem := getD_mem_matrixRows hi
        refine ⟨(hP1r _ hmem).1.le, fun e he ↦ ?_⟩
        obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
        have h1 := (hP1r _ hmem).2 j
        have h2 := PMDegree.val_size_le_natDegree_add_one (P₁.getD i #[])[j]
        rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at h1
        exact le_trans h2 (by simpa using Nat.add_le_add_right h1 1)
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
        exact rowWithin_empty _ _) shift (fun j ↦ by have := hIsh j; omega)
  have hMEb := PMFFT.mulEvalPC_cost P (by includes) p hp P₂ P₁ (o - d) d hP2D hP1D
    (clog2_le (by omega)) (by omega) (by omega) hP1pos (by omega) (by omega)
  have hshape := mulWith_shape fftMulLowContext.mulContext P₂ P₁ hP2D hP1D
  have hcomp : RT.composeBasis P₂ P₁ = mulWith fftMulLowContext.mulContext P₂ P₁ :=
    mulStrassenWith_eq_mulWith _ _ _ _
  have hCP := compactNonzeroRowsC_cost P (by includes) (C := r) (D := o + 1) (RT.composeBasis P₂ P₁)
    (fun row hrow ↦ by
      rw [hcomp] at hrow
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
      have := hshape.2 i
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)] at this
      have hw : o - d + d + 1 = o + 1 := by omega
      rw [hP1w, hw] at this
      simpa using this)
  have hCPs : (RT.composeBasis P₂ P₁).size = r := by rw [hcomp, hshape.1, hP2s']
  rw [hCPs] at hCP
  rw [hP1s] at hRM hUS
  rw [hmw] at hRM
  rw [hP2s', hP1s, hP1w] at hMEb
  rw [hP1s, hIs, hmw] at hMTb
  have hovh : 80 ≤ p.ovh := le_trans (by norm_num) (PMFFT.ovh_of_ok hp)
  have hglue := glue_le r m o p.ovh d hr hge hovh (by omega)
  have hl1 : limbCount (n + 1) = 1 := limbs_of_lt (by omega)
  have hl2 : limbCount o = 1 := limbs_of_lt (by omega)
  have hl3 : limbCount 1 = 1 := rfl
  have hq : (residualOrders problem d).size = problem.orders.size := Array.size_map ..
  rw [hl1, hl2, hl3]
  simp only [max_self]
  omega


/-- **The invariant passes to both children.** -/
theorem coreInv_children {r m SB : ℕ} (hr : 1 ≤ r) (hSB : SB < 2 ^ 62) (problem : XAdicProblem K) (shift : Array ℕ)
    (hI : CoreInv r m SB problem shift) (n : ℕ) (hge : 2 ≤ maxOrder problem)
    (hfuel : maxOrder problem ≤ n + 2) :
    CoreInv r m SB (pmLower problem) shift ∧
      CoreInv r m SB (pmResidual targetRT n problem shift) (pmShifted targetRT n problem shift) := by
  obtain ⟨hIs, hIrows, hIord, hIsz, hIsh, hI3⟩ := hI
  have hlo := maxOrder_pmLower problem
  have hre := maxOrder_pmResidual targetRT n problem shift
  refine ⟨⟨hIs, hIrows, by simp [pmLower, lowerOrders]; omega, hIsz, fun j ↦ by
    have := hIsh j; rw [hlo]; omega, by rw [hlo]; omega⟩, ?_⟩
  have hh := PMDegree.popovRuntime_core_node fftMulContext fftMulLowContext 1 (le_refl _) n problem
    shift hge hfuel
  dsimp only at hh
  obtain ⟨-, hd1, hd2, -, -, -, -, hP1s, hP1r, hRs, hRr, hRe, -, -⟩ := hh
  have hmw : MatrixWidth problem.matrix = m := matrixWidth_of_rows hIs hr hIrows
  unfold CoreInv
  rw [hre]
  simp only [pmResidual, pmShifted, pmLower, targetRT]
  rw [targetRT_eq']
  have hRP : (Popov.popovRuntime fftMulContext fftMulLowContext 1 1).residualProduct =
      mulTruncColumnStrassenWith fftMulLowContext 1 := rfl
  rw [hRP]
  set o := maxOrder problem with ho
  set d := o / 2 with hdd
  have hord : ∀ x ∈ problem.orders, x ≤ o := le_maxOrder problem
  refine ⟨hRs.trans hIs, fun row hrow ↦ (hRr row hrow).trans hmw,
    by simp [residualOrders]; omega, fun i j ↦ by
      have := hRe i j; have := getD_le_of_mem hord (j := j); have := hIsh 0; omega,
    fun j ↦ ?_, by omega⟩
  have hS : ∀ j, shift.getD j 0 ≤ SB - 2 * o := fun j ↦ by have := hIsh j; omega
  have := updateShiftByRows_getD_le
    (pmBasisWithFuelCore (Popov.popovRuntime fftMulContext fftMulLowContext 1 1) n
      { orders := lowerOrders problem d, matrix := problem.matrix } shift) shift
    (X := SB - 2 * o + (d + 1))
    (fun i v hv ↦ by
      have hw := rowWithin_of_rows (C := problem.matrix.size) (D := d + 1)
        (M := pmBasisWithFuelCore (Popov.popovRuntime fftMulContext fftMulLowContext 1 1) n
          { orders := lowerOrders problem d, matrix := problem.matrix } shift)
        (fun row hrow ↦ (hP1r row hrow).1.le)
        (fun i' j' ↦ by
          have h2 := PMDegree.val_size_le_natDegree_add_one
            (rowGet ((pmBasisWithFuelCore (Popov.popovRuntime fftMulContext fftMulLowContext 1 1) n
              { orders := lowerOrders problem d, matrix := problem.matrix } shift).getD i' #[]) j')
          have h1 := degLe_of_rows (fun row hrow j ↦ (hP1r row hrow).2 j) i' j'
          omega) i
      have := rowShiftedDegree?_le hw hS hv
      omega)
    (fun j ↦ by have := hS j; omega) j
  have := hIsh 0
  omega

/-- **The compiled PM-basis core's price** (`pmCoreC`, at CompPoly's fuel `pmBasisFuel`): on a
problem of the invariant (`r ≥ m` rows of width `m`, shifts plus twice the maximal order at most
`SB < 2^39`), with the products within the model (`mulEvalPC_cost`, `mulTruncEvalPC_cost`)
and the leaf within `Lc` (`LeafCost`), at most the model's tree with the node price
`pmNodePrice p r m` and the leaf price `Lc + 21·m + 32`, at prices `p` the products fit
(`FFTPricesOK p`). -/
theorem pmCoreC_cost (hP : Includes P pmCoreC.costDeps) {p : PMPrices} (hp : PMFFT.FFTPricesOK p)
    {r m SB Lc : ℕ} (hr : 2 ≤ r) (hm : m ≤ r)
    (hr30 : r < 2 ^ 30) (hSB : SB < 2 ^ 39) (hL : LeafCost P r m SB Lc)
    (problem : XAdicProblem K) (shift : Array ℕ) (hI : CoreInv r m SB problem shift) :
    machineCost P pmCoreC.costIdx
        [encodeValue (pmBasisFuel problem), encodeValue problem, encodeValue shift] ≤
      pmTree 1 (Lc + 21 * m + 32) (pmNodePrice p r m) (maxOrder problem) := by
  let T : ℕ → XAdicProblem K → Array ℕ → ℕ := fun fuel prob sh ↦
    if fuel < 2 ^ 61 then
      machineCost P pmCoreC.costIdx [encodeValue fuel, encodeValue prob, encodeValue sh]
    else 0
  have hlc : targetRT.leafCutoff = 1 := rfl
  have hord_lt : ∀ prob sh, CoreInv r m SB prob sh → maxOrder prob < 2 ^ 38 := fun prob sh h ↦ by
    have := h.2.2.2.2.1 0; omega
  have h := pmBasisFuel_price_le targetRT T (Lc + 21 * m + 32) (pmNodePrice p r m)
    (CoreInv r m SB)
    (fun fuel prob sh hIp hf hl ↦ by
      rw [hlc] at hl
      have hl' : maxOrder prob ≤ 1 := by omega
      have hleaf := hL prob sh hIp hl'
      have hMO := maxOrderC_cost P (by includes) prob (fun x hx ↦ by
        have := le_maxOrder prob x hx; omega)
      have hos := hIp.2.2.1
      show (if fuel < 2 ^ 61 then _ else 0) ≤ _
      split_ifs with hfu
      · cases fuel with
        | zero =>
          rw [pmCoreC.costEq_zero P hP]
          change machineCost P popovLeafC.costIdx _ +
            machineCost P compactNonzeroRowsC.costIdx [encodeValue (Popov.popovLeafBasis prob sh)] + 8 ≤ _
          omega
        | succ k =>
          rw [pmCoreC.costEq_succ P hP]
          have hd : decide (maxOrder prob ≤ (popovEvalRuntime novelTransform fftMulContext
              fftMulLowContext 1).leafCutoff) = true := by
            show decide (maxOrder prob ≤ 1) = true; simp; omega
          simp only [hd, Bool.true_or, ↓reduceIte]
          change _ + (machineCost P popovLeafC.costIdx _ +
            machineCost P compactNonzeroRowsC.costIdx [encodeValue (Popov.popovLeafBasis prob sh)] + 4) +
              15 ≤ _
          rw [limbs_of_lt (by omega : k + 1 < 2 ^ 64),
            limbs_of_lt (by have := hord_lt prob sh hIp; omega : maxOrder prob < 2 ^ 64)]
          have h1 : limbCount (popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1).leafCutoff =
            1 := rfl
          rw [h1]
          omega
      · omega)
    (fun fuel prob sh hIp hf hc h2 ↦ by
      obtain ⟨hl, hrs⟩ := coreInv_children (by omega) (by omega) prob sh hIp fuel h2 hf
      refine ⟨hl, hrs, ?_⟩
      show (if fuel + 1 < 2 ^ 61 then _ else 0) ≤ _ + (if fuel < 2 ^ 61 then _ else 0) +
        (if fuel < 2 ^ 61 then _ else 0)
      split_ifs with h1 h3
      · exact pmCoreC_node P hP hp hr hm hr30 hSB prob sh hIp fuel (by omega) h2 hf
      · omega
      · omega
      · omega)
    problem shift hI
  have hf : pmBasisFuel problem < 2 ^ 61 := by
    have := hord_lt problem shift hI; rw [pmBasisFuel]; omega
  have hT : T (pmBasisFuel problem) problem shift = machineCost P pmCoreC.costIdx
      [encodeValue (pmBasisFuel problem), encodeValue problem, encodeValue shift] := by
    simp only [T]
    split_ifs
    rfl
  rw [← hT]
  rwa [hlc] at h

end

end LeanVM.Cost.Bounds.PMCore
