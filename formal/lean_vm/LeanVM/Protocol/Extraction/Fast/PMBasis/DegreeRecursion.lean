module

public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeLeaf
public import LeanVM.Protocol.Extraction.Fast.PMBasis.PopovCore
import all CompPoly.Univariate.Basic

/-!
# Degree at most the order through the PM-basis recursion, and the residuals' sizes

CompPoly's PM-basis driver `pmBasisWithFuelCore` (`Approximant/PMBasis/Recursion.lean`) on
`leafRuntime mulCtx lowCtx leafCutoff c leaf` (`PopovCore.lean`: CompPoly's runtime with any leaf;
CompPoly's kernel-leaf runtime is the one on `kernelLeafBasis`, the target `popovRuntime` the one
on `popovLeafBasis`): at a problem of maximal order `o` it calls the leaf when `o ≤ leafCutoff` or
`o ≤ 1` (or the fuel is out), and otherwise, with `d₁ = o / 2`, computes `P₁` on the orders capped
at `d₁` (same matrix), the residual `R = (P₁·A) div X^d₁` truncated to the orders `oⱼ − d₁`
(`residualMatrixWithProduct`, by the column-truncated product `mulTruncColumnStrassenWith lowCtx c`
at the orders `(oⱼ − d₁) + d₁`), `P₂` on `R` under the shift `updateShiftByRows P₁ shift`, and
returns `compactNonzeroRows (P₂·P₁)` (`mulStrassenWith lowCtx c`, the exact product).

At `leafCutoff ≤ 1` and fuel at least `maxOrder − 1` (`pmBasisFuel = maxOrder + 1` is more than
enough), every leaf is at order at most one, and on a leaf of degree at most one there
(`LeafDegreeOne`: both leaves, `DegreeLeaf.lean`; the sorted leaf's rows are rows of CompPoly's)
`deg(P₂·P₁) ≤ (o − d₁) + d₁ = o`, so every entry of every basis the recursion returns has degree
at most `max 1 o` (**`leafRuntime_core_natDegree_le`**; `o ≥ 2` at every split, so both halves have
order at least one). The hypotheses are only these: the multiplication contexts carry their laws
as fields (`MulContext.mul_eq_mul`, `MulLowContext.mulLow_eq`), so the composition is the exact
product (`mulStrassenWith_eq_mulWith`) whatever context is plugged in, and no hypothesis on the
matrix, the shift or the orders is needed. With too little fuel a leaf runs at a cap `c > 1`, where
a cancellation multiplies by `X^Δ` with `Δ` up to about `c` and degrees can reach about `2c`.

Sizes (**`leafRuntime_core_node`**, for the cost proof): at a node, with `m` the problem's rows and
`A` its matrix, `P₁` has at most `m` rows, each of width `m`, entries of degree at most `d₁`; `R` has
exactly `P₁.size` rows, each of width `MatrixWidth A`, entry `(i, j)` with at most `oⱼ − d₁`
coefficients (`val.size`; zero for `j` beyond the orders); `P₂` has at most `R.size` rows, each of
width `R.size`, entries of degree at most `o − d₁`. Every core has at most `m` rows
(**`leafRuntime_core_size_le`**). On the target runtime the counts are exact
(**`popovRuntime_core_node`**: `P₁`, `R`, `P₂` with `m` rows; **`popovRuntime_core_spec`**: `m`
rows of width `m`, ordered weak Popov, degree at most
`max 1 o`, and `pmBasis` is the core, no root pass). On CompPoly's kernel-leaf runtime,
exactly `m` at an internal node would need `P₁`'s rows independent, which only the leaf's weak
Popov form gives (the composition lemma carries it on the sorted leaf).

Credits: the recursion and the lemmas used here are CompPoly's (github.com/Verified-zkEVM/CompPoly,
Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"; `LinearAlgebra/PolynomialMatrix/`, Valerii
Huhnin); the node's unfolding follows `pmBasisWithFuelCore_kernelLeaf_rows`.
-/

namespace LeanVM.Extraction.Fast.PMDegree

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Extraction.Fast.Popov (leafRuntime LeafRows leafRuntime_core_rows popovRuntime
  popovLeafBasis)
open DenseMatrix (array_getD_of_lt' array_getD_of_le')

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Orders of the two halves -/

theorem foldl_max_map {f : Nat → Nat} (hf : Monotone f) :
    ∀ (l : List Nat) (acc : Nat), (l.map f).foldl max (f acc) = f (l.foldl max acc) := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← hf.map_max, ih]

omit [Field F] [BEq F] [LawfulBEq F] in
theorem maxOrder_map [Zero F] (orders : Array Nat) {f : Nat → Nat} (hf : Monotone f)
    (h0 : f 0 = 0) (A : PolynomialMatrix F) :
    maxOrder ({ orders := orders.map f, matrix := A } : XAdicProblem F) =
      f (orders.foldl max 0) := by
  simp only [maxOrder]
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  have h := foldl_max_map hf orders.toList 0
  rwa [h0] at h

omit [BEq F] [LawfulBEq F] in
theorem maxOrder_lower (problem : XAdicProblem F) (d : Nat) (A : PolynomialMatrix F) :
    maxOrder ({ orders := lowerOrders problem d, matrix := A } : XAdicProblem F) =
      min (maxOrder problem) d :=
  maxOrder_map problem.orders (f := fun o ↦ min o d) (fun _ _ h ↦ min_le_min_right d h)
    (Nat.zero_min d) A

omit [BEq F] [LawfulBEq F] in
theorem maxOrder_residual (problem : XAdicProblem F) (d : Nat) (A : PolynomialMatrix F) :
    maxOrder ({ orders := residualOrders problem d, matrix := A } : XAdicProblem F) =
      maxOrder problem - d :=
  maxOrder_map problem.orders (f := fun o ↦ o - d) (fun _ _ h ↦ Nat.sub_le_sub_right h d)
    (Nat.zero_sub d) A

/-! ## Degrees of a product -/

/-- An entry of `p·P` has degree at most `a + b` when `p`'s entries have degree at most `a` and
`P`'s at most `b`. -/
theorem natDegree_rowGet_rowMulMatrixWith_le (ctx : CPolynomial.MulContext F)
    (p : PolynomialRow F) (P : PolynomialMatrix F) {a b : Nat}
    (hp : ∀ k, (rowGet p k).natDegree ≤ a)
    (hP : ∀ r ∈ MatrixRows P, ∀ j, (rowGet r j).natDegree ≤ b) (j : Nat) :
    (rowGet (rowMulMatrixWith ctx p P) j).natDegree ≤ a + b := by
  rcases Nat.lt_or_ge j (MatrixWidth P) with hj | hj
  · rw [rowGet_rowMulMatrixWith ctx p P hj, CPolynomial.natDegree_toPoly, pm_toPoly_finset_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
    rw [CPolynomial.toPoly_mul]
    refine Polynomial.natDegree_mul_le.trans (Nat.add_le_add ?_ ?_)
    · rw [← CPolynomial.natDegree_toPoly]
      exact hp k
    · rw [← CPolynomial.natDegree_toPoly]
      rcases Nat.lt_or_ge k P.size with hk | hk
      · exact hP _ (getD_mem_matrixRows hk) j
      · rw [array_getD_of_le' _ _ hk, rowGet, array_getD_of_le' _ _ (Nat.zero_le j),
          CPolynomial.natDegree_zero]
        exact Nat.zero_le b
  · rw [rowGet_rowMulMatrixWith_of_width_le ctx p P hj, CPolynomial.natDegree_zero]
    exact Nat.zero_le _

/-! ## The residual matrix -/

omit [Field F] [BEq F] [LawfulBEq F] in
theorem matrixWidth_eq_getD_size' [Zero F] (M : PolynomialMatrix F) :
    MatrixWidth M = (M.getD 0 #[]).size := by
  unfold MatrixWidth
  rw [Array.getD_eq_getD_getElem?]
  cases M[0]? <;> rfl

omit [BEq F] [LawfulBEq F] in
theorem val_size_le_natDegree_add_one (p : CPolynomial F) : p.val.size ≤ p.natDegree + 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

theorem val_size_divXTrunc_le (shift order : Nat) (p : CPolynomial F) :
    (divXTrunc shift order p).val.size ≤ order := by
  rw [divXTrunc, CPolynomial.ofArray]
  refine (CPolynomial.Raw.Trim.size_le_size _).trans ?_
  simp

/-- **The residual matrix's shape.** `R = (P·A) div X^d`, truncated to `orders`, by the
column-truncated product: `P.size` rows, each of width `MatrixWidth A`, entry `(i, j)` with at most
`orders[j]` coefficients, those of `X^t·(P·A)ᵢⱼ` for `t ≥ d`. -/
theorem residualMatrix_shape (lowCtx : MulLowContext F) (c : Nat) (P A : PolynomialMatrix F)
    (d : Nat) (orders : Array Nat) :
    (residualMatrixWithProduct (mulTruncColumnStrassenWith lowCtx c) P A d orders).size =
        P.size ∧
      (0 < P.size → MatrixWidth (residualMatrixWithProduct (mulTruncColumnStrassenWith lowCtx c)
        P A d orders) = MatrixWidth A) ∧
      (∀ r ∈ MatrixRows (residualMatrixWithProduct (mulTruncColumnStrassenWith lowCtx c)
        P A d orders), r.size = MatrixWidth A) ∧
      ∀ i j, (rowGet ((residualMatrixWithProduct (mulTruncColumnStrassenWith lowCtx c)
        P A d orders).getD i #[]) j).val.size ≤ orders.getD j 0 := by
  set prod := mulTruncColumnStrassenWith lowCtx c (orders.map fun order ↦ order + d) P A
    with hprod
  have hprodsize : prod.size = P.size := mulTruncColumnStrassenWith_size _ _ _ _ _
  have hprodwidth : 0 < P.size → MatrixWidth prod = MatrixWidth A := by
    intro hpos
    rw [matrixWidth_eq_getD_size', hprod, mulTruncColumnStrassenWith_eq_truncateColumns,
      truncateColumns_getD _ _ (by rw [mulWith_size]; exact hpos), mulWith_getD _ _ _ hpos]
    simp [rowTruncateColumns, rowMulMatrixWith_size]
  simp only [residualMatrixWithProduct]
  rw [← hprod]
  refine ⟨by rw [ofFn_size, hprodsize], fun hpos ↦ ?_, fun r hr ↦ ?_, fun i j ↦ ?_⟩
  · rw [MatrixWidth_ofFn, ite_eq_right (by omega), hprodwidth hpos]
  · rw [MatrixRows] at hr
    rcases List.getElem_of_mem hr with ⟨i, hi, rfl⟩
    have hi' : i < prod.size := by simpa [ofFn_size] using hi
    rw [Array.getElem_toList, ← array_getD_of_lt' _ _ (by simpa using hi), getD_ofFn,
      ite_eq_left hi']
    simp only [List.size_toArray, List.length_map, List.length_range]
    exact hprodwidth (by omega)
  · rw [rowGet_ofFn]
    split
    · exact val_size_divXTrunc_le _ _ _
    · exact Nat.zero_le _

/-! ## The recursion, on a leaf of degree at most one at order one -/

/-- The leaf has entries of degree at most one at order at most one. -/
@[expose] def LeafDegreeOne (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F) : Prop :=
  ∀ (problem : XAdicProblem F) (shift : Array Nat), maxOrder problem ≤ 1 →
    ∀ row ∈ MatrixRows (leaf problem shift), ∀ j, (rowGet row j).natDegree ≤ 1

/-- The leaf has at most `problem.matrix.size` rows. -/
@[expose] def LeafSizeLe (leaf : XAdicProblem F → Array Nat → PolynomialMatrix F) : Prop :=
  ∀ (problem : XAdicProblem F) (shift : Array Nat), (leaf problem shift).size ≤ problem.matrix.size

/-- **Degree at most the order through the recursion.** On CompPoly's runtime with a leaf of
degree at most one at order one (`leafRuntime`; CompPoly's kernel-leaf runtime is
the one on `kernelLeafBasis`), at `leafCutoff ≤ 1`, with fuel at least `maxOrder problem − 1`, every entry of every row of the
returned basis has degree at most `max 1 (maxOrder problem)`. -/
theorem leafRuntime_core_natDegree_le (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) {leafCutoff : Nat} (composeLeafCutoff : Nat)
    {leaf : XAdicProblem F → Array Nat → PolynomialMatrix F} (hdeg : LeafDegreeOne leaf)
    (hcut : leafCutoff ≤ 1) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      maxOrder problem ≤ fuel + 1 →
      ∀ row ∈ MatrixRows (pmBasisWithFuelCore
        (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf)
          fuel problem shift),
        ∀ j, (rowGet row j).natDegree ≤ max 1 (maxOrder problem) := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift hfuel row hrow j
      rw [pmBasisWithFuelCore] at hrow
      exact (hdeg problem shift (by omega) row (compactNonzeroRows_subset hrow) j).trans
        (Nat.le_max_left _ _)
  | succ fuel ih =>
      intro problem shift hfuel row hrow j
      rw [pmBasisWithFuelCore] at hrow
      split at hrow
      · rename_i hleaf
        have hleaf' : maxOrder problem ≤ leafCutoff ∨ maxOrder problem ≤ 1 := by
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hleaf
          exact hleaf
        have hle : maxOrder problem ≤ 1 := by omega
        exact (hdeg problem shift hle row (compactNonzeroRows_subset hrow) j).trans
          (Nat.le_max_left _ _)
      · rename_i hnode
        have hnode' : ¬(maxOrder problem ≤ leafCutoff ∨ maxOrder problem ≤ 1) := by
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hnode
          exact hnode
        have hge : 2 ≤ maxOrder problem := by omega
        set d₁ := maxOrder problem / 2 with hd₁
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
        rw [mulStrassenWith_eq_mulWith, matrixRows_mulWith] at hmem
        rcases List.mem_map.mp hmem with ⟨p₂, hp₂mem, rfl⟩
        have hlowmax : maxOrder lower = d₁ := by
          rw [hlower, maxOrder_lower]
          omega
        have hresmax : maxOrder residual = maxOrder problem - d₁ := by
          rw [hresidual, hresOrders, maxOrder_residual]
        have h1 := ih lower shift (by omega)
        have h2 := ih residual shifted (by omega) p₂ hp₂mem
        refine (natDegree_rowGet_rowMulMatrixWith_le _ p₂ P₁
          (a := maxOrder problem - d₁) (b := d₁) ?_ ?_ j).trans ?_
        · intro k
          have := h2 k
          rw [hresmax] at this
          omega
        · intro r hr j
          have := h1 r hr j
          rw [hlowmax] at this
          omega
        · omega

/-- At most `m` rows, on a leaf with at most `m` rows (any cutoff and fuel). -/
theorem leafRuntime_core_size_le (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff composeLeafCutoff : Nat)
    {leaf : XAdicProblem F → Array Nat → PolynomialMatrix F} (hleaf : LeafSizeLe leaf) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      (pmBasisWithFuelCore (leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf)
          fuel problem shift).size ≤ problem.matrix.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift
      rw [pmBasisWithFuelCore, compactNonzeroRows]
      exact Array.size_filter_le.trans (hleaf problem shift)
  | succ fuel ih =>
      intro problem shift
      rw [pmBasisWithFuelCore]
      split
      · rw [compactNonzeroRows]
        exact Array.size_filter_le.trans (hleaf problem shift)
      · simp only [leafRuntime]
        rw [compactNonzeroRows]
        refine Array.size_filter_le.trans ?_
        rw [mulStrassenWith_size]
        refine (ih _ _).trans ?_
        rw [(residualMatrix_shape _ _ _ _ _ _).1]
        exact ih _ _

omit [Field F] [BEq F] [LawfulBEq F] in
theorem residualOrders_getD [Zero F] (problem : XAdicProblem F) (d j : Nat) :
    (residualOrders problem d).getD j 0 = problem.orders.getD j 0 - d := by
  rw [residualOrders]
  rcases Nat.lt_or_ge j problem.orders.size with hj | hj
  · exact natArray_map_getD (fun o ↦ o - d) problem.orders hj
  · rw [array_getD_of_le' _ _ (by simpa using hj), array_getD_of_le' _ _ hj, Nat.zero_sub]

/-- **A node of the recursion, with the sizes the cost proof needs.** On `leafRuntime` with a
sound leaf (`LeafRows`) of at most `m` rows and degree at most one at order one, at
`leafCutoff ≤ 1`, at a problem of maximal order `o ≥ 2` with fuel `fuel + 1 ≥ o − 1`: the result is
`compactNonzeroRows (P₂·P₁)`; both halves have order at least one and within the fuel left; `P₁`
has at most `m` rows of width `m`, entries of degree at most `d₁`; the residual `R` has `P₁.size`
rows of width `MatrixWidth A`, entry `(i, j)` with at most `oⱼ − d₁` coefficients; `P₂` has at
most `R.size` rows of width `R.size`, entries of degree at most `o − d₁`. -/
theorem leafRuntime_core_node (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) {leafCutoff : Nat} (composeLeafCutoff : Nat)
    {leaf : XAdicProblem F → Array Nat → PolynomialMatrix F} (hrows : LeafRows mulCtx leaf)
    (hsize : LeafSizeLe leaf) (hdeg : LeafDegreeOne leaf)
    (hcut : leafCutoff ≤ 1) (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat)
    (hge : 2 ≤ maxOrder problem) (hfuel : maxOrder problem ≤ fuel + 2) :
    let RT := leafRuntime mulCtx lowCtx leafCutoff composeLeafCutoff leaf
    let o := maxOrder problem
    let d₁ := o / 2
    let lower : XAdicProblem F := { orders := lowerOrders problem d₁, matrix := problem.matrix }
    let P₁ := pmBasisWithFuelCore RT fuel lower shift
    let R := residualMatrixWithProduct (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
      problem.matrix d₁ (residualOrders problem d₁)
    let residual : XAdicProblem F := { orders := residualOrders problem d₁, matrix := R }
    let P₂ := pmBasisWithFuelCore RT fuel residual (updateShiftByRows P₁ shift)
    pmBasisWithFuelCore RT (fuel + 1) problem shift =
        compactNonzeroRows (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁) ∧
      1 ≤ d₁ ∧ 1 ≤ o - d₁ ∧ d₁ ≤ fuel + 1 ∧ o - d₁ ≤ fuel + 1 ∧
      maxOrder lower = d₁ ∧ maxOrder residual = o - d₁ ∧
      P₁.size ≤ problem.matrix.size ∧
      (∀ r ∈ MatrixRows P₁, r.size = problem.matrix.size ∧ ∀ j, (rowGet r j).natDegree ≤ d₁) ∧
      R.size = P₁.size ∧ (∀ r ∈ MatrixRows R, r.size = MatrixWidth problem.matrix) ∧
      (∀ i j, (rowGet (R.getD i #[]) j).val.size ≤ problem.orders.getD j 0 - d₁) ∧
      P₂.size ≤ R.size ∧
      (∀ r ∈ MatrixRows P₂, r.size = R.size ∧ ∀ j, (rowGet r j).natDegree ≤ o - d₁) := by
  intro RT o d₁ lower P₁ R residual P₂
  have hlowmax : maxOrder lower = d₁ := by
    simp only [lower, maxOrder_lower]
    omega
  have hresmax : maxOrder residual = o - d₁ := by
    simp only [residual, maxOrder_residual]
    rfl
  have hRshape := residualMatrix_shape lowCtx composeLeafCutoff P₁ problem.matrix d₁
    (residualOrders problem d₁)
  refine ⟨?_, by omega, by omega, by omega, by omega, hlowmax, hresmax, ?_, fun r hr ↦ ⟨?_, ?_⟩,
    hRshape.1, hRshape.2.2.1, fun i j ↦ ?_, ?_, fun r hr ↦ ⟨?_, ?_⟩⟩
  · rw [pmBasisWithFuelCore]
    have hnode : ¬((decide (maxOrder problem ≤ RT.leafCutoff) || decide (maxOrder problem ≤ 1)) =
        true) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      change ¬(maxOrder problem ≤ leafCutoff ∨ maxOrder problem ≤ 1)
      omega
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hnode)]
    rfl
  · exact leafRuntime_core_size_le mulCtx lowCtx leafCutoff composeLeafCutoff hsize fuel lower
      shift
  · exact (leafRuntime_core_rows mulCtx lowCtx leafCutoff composeLeafCutoff leaf hrows fuel
      lower shift r hr).2
  · intro j
    have h := leafRuntime_core_natDegree_le mulCtx lowCtx composeLeafCutoff hdeg hcut fuel lower
      shift (by omega) r hr j
    rw [hlowmax] at h
    omega
  · rw [← residualOrders_getD]
    exact hRshape.2.2.2 i j
  · exact leafRuntime_core_size_le mulCtx lowCtx leafCutoff composeLeafCutoff hsize fuel
      residual _
  · exact (leafRuntime_core_rows mulCtx lowCtx leafCutoff composeLeafCutoff leaf hrows fuel
      residual _ r hr).2
  · intro j
    have h := leafRuntime_core_natDegree_le mulCtx lowCtx composeLeafCutoff hdeg hcut fuel
      residual _ (by omega) r hr j
    rw [hresmax] at h
    omega

/-! ## The leaf sorted by pivot: the target runtime -/

theorem popovLeafBasis_leafDegreeOne : LeafDegreeOne (popovLeafBasis (F := F)) :=
  fun problem shift h row hrow ↦ kernelLeafBasis_natDegree_le_one problem shift h row
    (Popov.mem_kernelLeafBasis_of_mem_popovLeafBasis problem shift hrow)

theorem popovLeafBasis_leafSizeLe : LeafSizeLe (popovLeafBasis (F := F)) :=
  fun problem shift ↦ (Popov.fillPivotSlots_size problem shift _).le

/-- **The target runtime** (`popovRuntime` at `leafCutoff ≤ 1`, any composition cutoff), at fuel
at least `maxOrder − 1`: exactly `m` rows, ordered weak Popov, every entry of degree at most
`max 1 (maxOrder problem)`. At CompPoly's fuel `pmBasisFuel` this core is `pmBasis` itself
(`pmBasis_popovRuntime_eq_core`) and the basis of `popovCorePMBasisContextWithLowAndCompose`. -/
theorem popovRuntime_core_spec (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) {leafCutoff : Nat} (composeLeafCutoff : Nat)
    (hcut : leafCutoff ≤ 1) (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat)
    (hfuel : maxOrder problem ≤ fuel + 1) :
    let B := pmBasisWithFuelCore (popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff) fuel
      problem shift
    B.size = problem.matrix.size ∧ Popov.OrderedWeakPopov B shift problem.matrix.size ∧
      ∀ row ∈ MatrixRows B, row.size = problem.matrix.size ∧
        ∀ j, (rowGet row j).natDegree ≤ max 1 (maxOrder problem) := by
  intro B
  have hP := Popov.popovRuntime_core_orderedWeakPopov mulCtx lowCtx leafCutoff composeLeafCutoff
    fuel problem shift
  refine ⟨hP.1, hP, fun row hrow ↦ ⟨(leafRuntime_core_rows mulCtx lowCtx leafCutoff
    composeLeafCutoff popovLeafBasis (Popov.popovLeafBasis_leafRows mulCtx) fuel problem shift
    row hrow).2, leafRuntime_core_natDegree_le mulCtx lowCtx composeLeafCutoff
      popovLeafBasis_leafDegreeOne hcut fuel problem shift hfuel row hrow⟩⟩

/-- **A node of the target runtime**, with exact sizes: `leafRuntime_core_node` on `popovRuntime`,
where every core has exactly `m` rows (`P₁`: `m`; `R`: `m` rows; `P₂`: `m` rows of width `m`). -/
theorem popovRuntime_core_node (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) {leafCutoff : Nat} (composeLeafCutoff : Nat)
    (hcut : leafCutoff ≤ 1) (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat)
    (hge : 2 ≤ maxOrder problem) (hfuel : maxOrder problem ≤ fuel + 2) :
    let RT := popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff
    let o := maxOrder problem
    let d₁ := o / 2
    let lower : XAdicProblem F := { orders := lowerOrders problem d₁, matrix := problem.matrix }
    let P₁ := pmBasisWithFuelCore RT fuel lower shift
    let R := residualMatrixWithProduct (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
      problem.matrix d₁ (residualOrders problem d₁)
    let residual : XAdicProblem F := { orders := residualOrders problem d₁, matrix := R }
    let P₂ := pmBasisWithFuelCore RT fuel residual (updateShiftByRows P₁ shift)
    pmBasisWithFuelCore RT (fuel + 1) problem shift =
        compactNonzeroRows (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁) ∧
      1 ≤ d₁ ∧ 1 ≤ o - d₁ ∧ d₁ ≤ fuel + 1 ∧ o - d₁ ≤ fuel + 1 ∧
      maxOrder lower = d₁ ∧ maxOrder residual = o - d₁ ∧
      P₁.size = problem.matrix.size ∧
      (∀ r ∈ MatrixRows P₁, r.size = problem.matrix.size ∧ ∀ j, (rowGet r j).natDegree ≤ d₁) ∧
      R.size = problem.matrix.size ∧ (∀ r ∈ MatrixRows R, r.size = MatrixWidth problem.matrix) ∧
      (∀ i j, (rowGet (R.getD i #[]) j).val.size ≤ problem.orders.getD j 0 - d₁) ∧
      P₂.size = problem.matrix.size ∧
      (∀ r ∈ MatrixRows P₂, r.size = problem.matrix.size ∧
        ∀ j, (rowGet r j).natDegree ≤ o - d₁) := by
  intro RT o d₁ lower P₁ R residual P₂
  have h := leafRuntime_core_node mulCtx lowCtx composeLeafCutoff
    (Popov.popovLeafBasis_leafRows mulCtx) popovLeafBasis_leafSizeLe popovLeafBasis_leafDegreeOne
    hcut fuel problem shift hge hfuel
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, _, h8, h9, h10, h11, _, h13⟩ := h
  have hP₁ : P₁.size = problem.matrix.size :=
    (Popov.popovRuntime_core_orderedWeakPopov mulCtx lowCtx leafCutoff composeLeafCutoff fuel
      lower shift).1
  have hP₂ : P₂.size = R.size :=
    (Popov.popovRuntime_core_orderedWeakPopov mulCtx lowCtx leafCutoff composeLeafCutoff fuel
      residual _).1
  have hR : R.size = problem.matrix.size := h9.trans hP₁
  refine ⟨h0, h1, h2, h3, h4, h5, h6, hP₁, h8, hR, h10, h11, hP₂.trans hR, fun r hr ↦ ?_⟩
  obtain ⟨hs, hd⟩ := h13 r hr
  exact ⟨hs.trans hR, hd⟩

end

end LeanVM.Extraction.Fast.PMDegree
