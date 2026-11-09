module

public import LeanVM.Protocol.Extraction.Extractor
public import Mathlib.Data.List.Find
public import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Completeness
public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Lemmas
public import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
public import CompPoly.Univariate.Roots.Shoup.Correctness
public import CompPoly.Univariate.Vanishing
public import CompPoly.Univariate.Context
public import CompPoly.Univariate.Raw.Context
public import CompPoly.Univariate.BatchEval.Context
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast
public import LeanVM.Protocol.Extraction.Fast.LeeRows
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Basic

/-!
# The lane decoder's CompPoly steps, restated

The fast lane decoder (`Fast/Extract.lean`: `interpContext`, Lee–O'Sullivan with
Mulders–Storjohann, the proof side's reference; `gsRunNoCheck`, Roth–Ruckenstein over
`fieldRootCtx`; the compiled decoder's interpolation is the approximant basis, `Fast/LanePM.lean`,
with the normalization below) calls CompPoly functions
whose code is asymptotically wasteful, so that a cost machine pricing the code honestly would
charge more than the algorithm needs. Each is restated here, self-contained, and proved equal to
CompPoly's, so its callers can be restated in turn.

* **Normalizing the interpolated polynomial** (`normalizeLeeFast`, **`normalizeLeeFast_eq`**).
  CompPoly's `normalizeLeeCandidate?` lists the `(W + 1)²` grid of monomials `X^x·Y^y`, `x, y ≤ W`,
  keeps those with `x + w·y ≤ W` (`interpolationMonomials`, `w = k − 1`), reads `Q`'s coefficient at
  each, divides by the first nonzero one, and rebuilds the polynomial by adding the `N` monomials
  one by one to a dense accumulator (`ofMonomialCoeffs`), about `N²` operations. `normalizeLeeFast`
  scans `Q`'s rows within the grid for the first nonzero coefficient `c` (`Y`-degree first, then
  `X`-degree, the grid's order: `leePivot?`) and builds `Q` restricted to the grid, divided by `c`,
  row by row (`leeScaled`): linear in `Q`'s size. Proved by coefficients (`coeff_leeScaled`, and
  `coeff_ofMonomialCoeffs_map_of_mem`, `coeff_ofMonomialCoeffs_of_not_mem` for CompPoly's), with no
  hypothesis on `Q`. Lee–O'Sullivan's interpolation with it: `leeOSullivanInterpolateFast`,
  `leeOSullivanInterpContextFast` (**`leeOSullivanInterpContextFast_eq`**).
* **Monic remainders** (`rawModContext_remainderOnly_eq_naive`).
  The root finder (`finiteFieldRootContext`, Shoup's splitter, the `X^q mod p` powers) reduces with
  `CPolynomial.Raw.ModContext.naive`, `modByMonic = (divModByMonicAux p q).2`: long division
  computing the quotient too, each step a general product `C(c)·(q·X^k)`. CompPoly's
  `ModContext.remainderOnly` (`modByMonicRemainderOnly`: one scaled subtraction per step) is equal
  as a context (`modByMonicRemainderOnly_eq_modByMonic` holds for every input). The Euclidean
  gcd's hard-wired `p % q` (`CPolynomial.Raw.mod`) with the remainder-only division: `rawModFast`,
  `rawGcdMonicFast`, `gcdMonicFast` (**`gcdMonicFast_eq`**). The root finder with these:
  `Fast/RootFinder.lean`.
* **The vanishing polynomial** (`vanishingFast`, **`vanishingFast_eq`**). CompPoly's
  `vanishingPolynomialArray` multiplies `acc * (X − x)`; the schoolbook product folds over its first
  operand, adding a shifted copy of the second to an accumulator as long as the result, so each
  step costs `|acc|²` and the fold `n³/3`. `vanishingFast` multiplies `(X − x) * acc`: `2·|acc|` per
  step, `n²` in all. Its context: `vanishingContextFast` (`vanishingContextFast_eq`).

* **The basis rows** (`leeRowsFast`, `Fast/LeeRows.lean`, **`leeRowsFast_eq`**): the powers of
  `Y − R` and of `G` computed once, not per row.

The decoder's interpolation with these: `interpContextFast` (**`interpContextFast_eq`**: it is
`interpContext`'s body).

* **Distinct points** (`interpolateDistinct`, **`interpolateDistinct_eq`**): the interpolation
  without its distinctness check (`distinctXCoordinatesBool`, `n²/2` comparisons), equal on
  distinct points, as the lane decoder's are.
* **Horner's rule** (`hornerEval`, **`hornerEval_eq`**): CompPoly's `CPolynomial.eval` computes each
  power `x^i` anew; the distance filter (`passesDistanceFast`, **`passesDistanceFast_eq`**) and
  the conversion to the novel basis (`toNovelFast`, **`toNovelFast_eq`**) evaluate by Horner.

Credits: copied from CompPoly (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"
and "Copyright (c) 2025 CompPoly"), and edited (the function called): the texts of
`leeOSullivanPositiveInterpolate` and `leeOSullivanInterpolate`
(`Bivariate/GuruswamiSudan/Interpolation/LeeOSullivan/Algorithm.lean`, Valerii Huhnin),
`gcdMonicWithFuel`, `gcdMonic` and `mod` (`Univariate/Raw/Division.lean`, Quang Dao, Gregor
Mitscha-Baude, Derek Sorensen, Desmond Coles, Valerii Huhnin) and `vanishingPolynomialArray`
(`Univariate/Vanishing.lean`, Valerii Huhnin). Used, not copied: `ofMonomialCoeffs_coeff`,
`ofMonomialCoeffs_coeff_getD`, `monomialsWeightedDegreeLE_nodup`, `foldl_range_eq_zero_of_zero`
(`Bivariate/GuruswamiSudan/PolynomialCorrectness.lean`), `cbivar_coeff_eq_zero_of_y_size_le`,
`modByMonicRemainderOnly_eq_modByMonic`, `ModContext.remainderOnly`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters
open CompPoly CompPoly.GuruswamiSudan CompPoly.CPolynomial.Roots.FiniteField

public section

/-! ## Searches over ranges -/

theorem findSome?_congr_mem {α β : Type*} {f g : α → Option β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a (by simp),
      ih fun b hb ↦ h b (by simp [hb])]

/-- A search over `range n` that finds nothing from `m` on is the search over `range m`. -/
theorem findSome?_range_of_none {β : Type*} {f : ℕ → Option β} {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → f i = none) :
    (List.range n).findSome? f = (List.range m).findSome? f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [List.range_add, List.findSome?_append]
  have htail : ((List.range d).map (m + ·)).findSome? f = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 ha
    exact h (m + a) (by omega) (by omega)
  rw [htail, Option.or_none]

theorem find?_range_of_false {p : ℕ → Bool} {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → p i = false) :
    (List.range n).find? p = (List.range m).find? p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [List.range_add, List.find?_append]
  have htail : ((List.range d).map (m + ·)).find? p = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 ha
    simp [h (m + a) (by omega) (by omega)]
  rw [htail, Option.or_none]

theorem findSome?_range_congr {β : Type*} {f g : ℕ → Option β} {m n : ℕ} (hmn : m ≤ n)
    (heq : ∀ i, i < m → f i = g i) (hnone : ∀ i, m ≤ i → i < n → f i = none) :
    (List.range n).findSome? f = (List.range m).findSome? g := by
  rw [findSome?_range_of_none hmn hnone]
  exact findSome?_congr_mem fun i hi ↦ heq i (List.mem_range.1 hi)

theorem find?_range_congr {p q : ℕ → Bool} {m n : ℕ} (hmn : m ≤ n)
    (heq : ∀ i, i < m → p i = q i) (hfalse : ∀ i, m ≤ i → i < n → p i = false) :
    (List.range n).find? p = (List.range m).find? q := by
  rw [find?_range_of_false hmn hfalse]
  exact List.find?_congr fun i hi ↦ heq i (List.mem_range.1 hi)

theorem find?_filter_and {α : Type*} (p q : α → Bool) (l : List α) :
    (l.filter p).find? q = l.find? fun a ↦ p a && q a := by
  rw [List.find?_filter]
  exact List.find?_congr fun a _ ↦ by cases p a <;> cases q a <;> rfl

/-- The first nonzero entry of a list, found by index or by value. -/
theorem find?_range_getD {F : Type*} [Zero F] [BEq F] [LawfulBEq F] (l : List F) :
    ((List.range l.length).find? fun i ↦ !(l.getD i 0 == 0)).map (fun i ↦ l.getD i 0) =
      l.find? fun a ↦ !(a == 0) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, List.find?_cons]
    by_cases ha : a = 0
    · subst ha
      simp only [List.getD_cons_zero, beq_self_eq_true, Bool.not_true, List.find?_map,
        Option.map_map, Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_succ]
      exact ih
    · have hb : (a == 0) = false := by simpa using ha
      simp only [List.getD_cons_zero, hb, Bool.not_false, Option.map_some]

/-- `normalizeVector?`: the first nonzero entry `c`, and the vector divided by it. -/
theorem normalizeVector?_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] (v : Array F) :
    normalizeVector? v = (v.toList.find? fun a ↦ !(a == 0)).map fun c ↦ v.map (· / c) := by
  have hg : ∀ i, v.getD i 0 = v.toList.getD i 0 := fun i ↦ by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hkey : (firstNonzeroIndex? v).map (fun i ↦ v.getD i 0) =
      v.toList.find? fun a ↦ !(a == 0) := by
    rw [← find?_range_getD]
    unfold firstNonzeroIndex?
    simp only [hg, Array.length_toList]
  unfold normalizeVector?
  cases h : firstNonzeroIndex? v with
  | none =>
    rw [h, Option.map_none] at hkey
    simp only [← hkey, Option.map_none]
  | some i =>
    rw [h, Option.map_some] at hkey
    have hne : v.getD i 0 ≠ 0 := by simpa using List.find?_some hkey.symm
    have hne' : (v.getD i 0 == 0) = false := by simpa using hne
    simp only [← hkey, Option.map_some, hne']
    rfl

/-! ## The interpolation's monomials -/

theorem mem_monomialGrid {W i j : ℕ} :
    (⟨i, j⟩ : CBivariate.Monomial) ∈ CBivariate.monomialGrid W ↔ i ≤ W ∧ j ≤ W := by
  unfold CBivariate.monomialGrid
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, CBivariate.Monomial.mk.injEq]
  constructor
  · rintro ⟨y, hy, x, hx, rfl, rfl⟩
    omega
  · rintro ⟨hi, hj⟩
    exact ⟨j, by omega, i, by omega, rfl, rfl⟩

/-- The interpolation's monomials: `y ≤ W` and `x + w·y ≤ W`. -/
theorem mem_interpolationMonomials {params : GSInterpParams} {i j : ℕ} :
    (⟨i, j⟩ : CBivariate.Monomial) ∈ (interpolationMonomials params).toList ↔
      j ≤ params.weightedDegreeBound ∧
        i + yWeight params * j ≤ params.weightedDegreeBound := by
  show (⟨i, j⟩ : CBivariate.Monomial) ∈
      (CBivariate.monomialGrid params.weightedDegreeBound).filter (fun m ↦
        decide (1 * m.xDegree + yWeight params * m.yDegree ≤ params.weightedDegreeBound)) ↔ _
  simp only [List.mem_filter, mem_monomialGrid, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, hj⟩, h⟩
    exact ⟨hj, by omega⟩
  · rintro ⟨hj, h⟩
    exact ⟨⟨by omega, hj⟩, by omega⟩

/-- At a listed monomial, the polynomial assembled from `ms.map h` has coefficient `h`. -/
theorem coeff_ofMonomialCoeffs_map_of_mem {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] {ms : Array CBivariate.Monomial} (hnd : ms.toList.Nodup)
    (h : CBivariate.Monomial → F) {i j : ℕ}
    (hm : (⟨i, j⟩ : CBivariate.Monomial) ∈ ms.toList) :
    CBivariate.coeff (CBivariate.ofMonomialCoeffs ms (ms.map h)) i j = h ⟨i, j⟩ := by
  obtain ⟨k, hk, hkm⟩ := List.mem_iff_getElem.1 hm
  have hk' : k < ms.size := by simpa using hk
  have hget : ms.getD k ⟨0, 0⟩ = ⟨i, j⟩ := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some]
    simpa using hkm
  have key := CBivariate.ofMonomialCoeffs_coeff_getD (coeffs := ms.map h) hnd hk'
  rw [hget] at key
  refine key.trans ?_
  rw [← hget]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']

/-- Off the listed monomials, the assembled polynomial is zero. -/
theorem coeff_ofMonomialCoeffs_of_not_mem {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] {ms : Array CBivariate.Monomial} (coeffs : Array F) {i j : ℕ}
    (hm : (⟨i, j⟩ : CBivariate.Monomial) ∉ ms.toList) :
    CBivariate.coeff (CBivariate.ofMonomialCoeffs ms coeffs) i j = 0 := by
  rw [CBivariate.ofMonomialCoeffs_coeff]
  apply DenseMatrix.foldl_range_eq_zero_of_zero
  intro col hcol
  have hmem : ms.getD col ⟨0, 0⟩ ∈ ms.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hcol, Option.getD_some]
    exact Array.getElem_mem_toList hcol
  have hmatch :
      ¬(i = (ms.getD col ⟨0, 0⟩).xDegree ∧ j = (ms.getD col ⟨0, 0⟩).yDegree) := by
    rintro ⟨rfl, rfl⟩
    exact hm hmem
  show (if i = (ms.getD col ⟨0, 0⟩).xDegree ∧ j = (ms.getD col ⟨0, 0⟩).yDegree then
      coeffs.getD col 0 else 0) = 0
  exact ite_eq_right hmatch

/-! ## Normalizing the interpolated polynomial -/

/-- The rows of `Q` the grid reaches: `y ≤ W`, and `y < |Q|` (beyond, the rows are zero). -/
@[expose] def leeRows {F : Type*} [Zero F] (params : GSInterpParams) (Q : CBivariate F) : ℕ :=
  min (params.weightedDegreeBound + 1) Q.val.size

/-- The columns of row `y` the grid reaches: `x + w·y ≤ W`, and `x < |Q_y|`. -/
@[expose] def leeCols {F : Type*} [Zero F] (params : GSInterpParams) (Q : CBivariate F)
    (y : ℕ) : ℕ :=
  min (params.weightedDegreeBound + 1 - yWeight params * y) (Q.val.coeff y).val.size

/-- The first monomial of the grid, `Y`-degree first, then `X`-degree, at which `Q` is
nonzero: the row scan stops at the first nonzero coefficient. -/
@[expose] def leePivot? {F : Type*} [Zero F] [BEq F] (params : GSInterpParams)
    (Q : CBivariate F) : Option CBivariate.Monomial :=
  (List.range (leeRows params Q)).findSome? fun y ↦
    ((List.range (leeCols params Q y)).find? fun x ↦ !(CBivariate.coeff Q x y == 0)).map
      fun x ↦ ⟨x, y⟩

/-- `Q` restricted to the grid, each coefficient divided by `c`, built row by row. -/
@[expose] def leeScaled {F : Type*} [Field F] [BEq F] [LawfulBEq F] (params : GSInterpParams)
    (Q : CBivariate F) (c : F) : CBivariate F :=
  CPolynomial.ofFn fun y : Fin (leeRows params Q) ↦
    CPolynomial.ofFn fun x : Fin (leeCols params Q y) ↦ CBivariate.coeff Q x y / c

/-- **`normalizeLeeCandidate?`, fast**: `Q` restricted to the interpolation's monomials,
divided by its first nonzero coefficient there; `none` if there is none. -/
@[expose] def normalizeLeeFast {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (params : GSInterpParams) (Q : CBivariate F) : Option (CBivariate F) :=
  (leePivot? params Q).map fun m ↦ leeScaled params Q (CBivariate.coeff Q m.xDegree m.yDegree)

theorem coeff_eq_zero_of_x_size_le {F : Type*} [Zero F] (Q : CBivariate F) {i j : ℕ}
    (hi : (Q.val.coeff j).val.size ≤ i) : CBivariate.coeff Q i j = 0 :=
  CPolynomial.coeff_eq_zero_of_size_le (Q.val.coeff j) hi

theorem coeff_leeScaled {F : Type*} [Field F] [BEq F] [LawfulBEq F] (params : GSInterpParams)
    (Q : CBivariate F) (c : F) (i j : ℕ) :
    CBivariate.coeff (leeScaled params Q c) i j =
      if j ≤ params.weightedDegreeBound ∧ i + yWeight params * j ≤ params.weightedDegreeBound
      then CBivariate.coeff Q i j / c else 0 := by
  rw [CBivariate.coeff_eq_coeff_coeff (leeScaled params Q c), leeScaled, CPolynomial.coeff_ofFn]
  by_cases hj : j < leeRows params Q
  · rewrite [dite_eq_left hj]
    dsimp only
    rw [CPolynomial.coeff_ofFn]
    by_cases hi : i < leeCols params Q j
    · have hreg : j ≤ params.weightedDegreeBound ∧
          i + yWeight params * j ≤ params.weightedDegreeBound := by
        unfold leeRows at hj
        unfold leeCols at hi
        omega
      rewrite [dite_eq_left hi, ite_eq_left hreg]
      rfl
    · rw [dite_eq_right hi]
      by_cases hreg : j ≤ params.weightedDegreeBound ∧
          i + yWeight params * j ≤ params.weightedDegreeBound
      · unfold leeCols at hi
        rw [ite_eq_left hreg, coeff_eq_zero_of_x_size_le Q (i := i) (j := j) (by omega), zero_div]
      · rw [ite_eq_right hreg]
  · rw [dite_eq_right hj, CPolynomial.coeff_zero]
    by_cases hreg : j ≤ params.weightedDegreeBound ∧
        i + yWeight params * j ≤ params.weightedDegreeBound
    · unfold leeRows at hj
      rw [ite_eq_left hreg, cbivar_coeff_eq_zero_of_y_size_le Q (i := i) (j := j) (by omega),
        zero_div]
    · rw [ite_eq_right hreg]

/-- The grid's first nonzero monomial is the row scan's. -/
theorem find?_interpolationMonomials {F : Type*} [Zero F] [BEq F] [LawfulBEq F]
    (params : GSInterpParams) (Q : CBivariate F) :
    (interpolationMonomials params).toList.find?
        (fun m ↦ !(CBivariate.coeff Q m.xDegree m.yDegree == 0)) = leePivot? params Q := by
  have hbasis : (interpolationMonomials params).toList =
      ((List.range (params.weightedDegreeBound + 1)).flatMap fun y ↦
          (List.range (params.weightedDegreeBound + 1)).map fun x ↦
            (⟨x, y⟩ : CBivariate.Monomial)).filter fun m ↦
        decide (1 * m.xDegree + yWeight params * m.yDegree ≤ params.weightedDegreeBound) := rfl
  rw [hbasis, find?_filter_and, List.find?_flatMap, leePivot?]
  refine findSome?_range_congr (m := leeRows params Q) (n := params.weightedDegreeBound + 1)
    (by unfold leeRows; omega) (fun y _hy ↦ ?_) (fun y hy₁ hy₂ ↦ ?_)
  · show ((List.range (params.weightedDegreeBound + 1)).map fun x ↦
          (⟨x, y⟩ : CBivariate.Monomial)).find?
          (fun m ↦ decide (1 * m.xDegree + yWeight params * m.yDegree ≤
              params.weightedDegreeBound) &&
            !(CBivariate.coeff Q m.xDegree m.yDegree == 0)) =
        ((List.range (leeCols params Q y)).find? fun x ↦ !(CBivariate.coeff Q x y == 0)).map
          fun x ↦ ⟨x, y⟩
    rw [List.find?_map]
    congr 1
    refine find?_range_congr (m := leeCols params Q y) (n := params.weightedDegreeBound + 1)
      (by unfold leeCols; omega) (fun x hx ↦ ?_) (fun x hx₁ _hx₂ ↦ ?_)
    · show (decide (1 * x + yWeight params * y ≤ params.weightedDegreeBound) &&
          !(CBivariate.coeff Q x y == 0)) = !(CBivariate.coeff Q x y == 0)
      unfold leeCols at hx
      rewrite [decide_eq_true (by omega :
        1 * x + yWeight params * y ≤ params.weightedDegreeBound)]
      rfl
    · show (decide (1 * x + yWeight params * y ≤ params.weightedDegreeBound) &&
          !(CBivariate.coeff Q x y == 0)) = false
      unfold leeCols at hx₁
      by_cases hreg : 1 * x + yWeight params * y ≤ params.weightedDegreeBound
      · have hz : CBivariate.coeff Q x y = 0 :=
          coeff_eq_zero_of_x_size_le Q (i := x) (j := y) (by omega)
        rw [hz]
        simp
      · rewrite [decide_eq_false hreg]
        rfl
  · show ((List.range (params.weightedDegreeBound + 1)).map fun x ↦
          (⟨x, y⟩ : CBivariate.Monomial)).find?
          (fun m ↦ decide (1 * m.xDegree + yWeight params * m.yDegree ≤
              params.weightedDegreeBound) &&
            !(CBivariate.coeff Q m.xDegree m.yDegree == 0)) = none
    unfold leeRows at hy₁
    have hz : ∀ x, CBivariate.coeff Q x y = 0 := fun x ↦
      cbivar_coeff_eq_zero_of_y_size_le Q (i := x) (j := y) (by omega)
    rw [List.find?_eq_none]
    intro m hm
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
    show ¬((decide (1 * x + yWeight params * y ≤ params.weightedDegreeBound) &&
      !(CBivariate.coeff Q x y == 0)) = true)
    rw [hz x]
    simp

/-- **`normalizeLeeFast` is CompPoly's `normalizeLeeCandidate?`**, on every input. -/
theorem normalizeLeeFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (params : GSInterpParams) (Q : CBivariate F) :
    normalizeLeeFast params Q = LeeOSullivan.normalizeLeeCandidate? params Q := by
  have hl : (interpolationCoefficientVector params Q).toList =
      (interpolationMonomials params).toList.map fun m ↦
        CBivariate.coeff Q m.xDegree m.yDegree := by
    rw [interpolationCoefficientVector, interpolationCoefficientVectorOnBasis, Array.toList_map]
  have hv : normalizeVector? (interpolationCoefficientVector params Q) =
      (leePivot? params Q).map fun m ↦
        (interpolationCoefficientVector params Q).map
          (· / CBivariate.coeff Q m.xDegree m.yDegree) := by
    rewrite [normalizeVector?_eq, hl, List.find?_map, Option.map_map,
      ← find?_interpolationMonomials]
    rfl
  rw [normalizeLeeFast, LeeOSullivan.normalizeLeeCandidate?, normalizeInterpolationPolynomial?,
    normalizeInterpolationPolynomialOnBasis?, hv]
  cases leePivot? params Q with
  | none => rfl
  | some m =>
    show some (leeScaled params Q (CBivariate.coeff Q m.xDegree m.yDegree)) =
      some (interpolationPolynomialOnBasis (interpolationMonomials params)
        ((interpolationCoefficientVector params Q).map
          (· / CBivariate.coeff Q m.xDegree m.yDegree)))
    congr 1
    refine CBivariate.eq_iff_coeff.2 fun i j ↦ ?_
    rw [coeff_leeScaled, interpolationPolynomialOnBasis, interpolationCoefficientVector,
      interpolationCoefficientVectorOnBasis, Array.map_map]
    by_cases hreg : j ≤ params.weightedDegreeBound ∧
        i + yWeight params * j ≤ params.weightedDegreeBound
    · rw [ite_eq_left hreg]
      exact (coeff_ofMonomialCoeffs_map_of_mem (F := F) (ms := interpolationMonomials params)
        (h := fun n ↦ CBivariate.coeff Q n.xDegree n.yDegree / CBivariate.coeff Q m.xDegree m.yDegree)
        (CBivariate.monomialsWeightedDegreeLE_nodup 1 (yWeight params)
          params.weightedDegreeBound) (mem_interpolationMonomials.2 hreg)).symm
    · rw [ite_eq_right hreg]
      exact (coeff_ofMonomialCoeffs_of_not_mem (ms := interpolationMonomials params) _
        fun hm ↦ hreg (mem_interpolationMonomials.1 hm)).symm

theorem normalizeLeeFast_eq_fun {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] :
    (normalizeLeeFast : GSInterpParams → CBivariate F → Option (CBivariate F)) =
      LeeOSullivan.normalizeLeeCandidate? := by
  funext params Q
  exact normalizeLeeFast_eq params Q

/-! ## Lee–O'Sullivan's interpolation with the fast normalization -/

/-- CompPoly's `leeOSullivanPositiveInterpolate` after its distinctness check, with the basis rows
`leeRowsFast` (`Fast/LeeRows.lean`) and `normalizeLeeFast`. -/
@[expose] def leeOSullivanPositiveCoreFast {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (reducer : PolynomialMatrix.ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) : Option (CBivariate F) :=
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
  let basis := leeRowsFast R G params
  let shift := leeOSullivanShifts params
  let reduced := reducer.reduce basis shift
  match LeeOSullivan.leastShiftedDegreeRow? reduced shift with
  | none => none
  | some row =>
      match PolynomialMatrix.rowShiftedDegree? row shift with
      | none => none
      | some degree =>
          if degree ≤ params.weightedDegreeBound then
            let rawQ := CBivariate.ofCoeffRow row
            match normalizeLeeFast params rawQ with
            | none => none
            | some Q => some Q
          else
            none

/-- CompPoly's `leeOSullivanPositiveInterpolate`, with `normalizeLeeFast`. -/
@[expose] def leeOSullivanPositiveInterpolateFast {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (reducer : PolynomialMatrix.ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) : Option (CBivariate F) :=
  if distinctXCoordinatesBool points then leeOSullivanPositiveCoreFast V E reducer points params
  else none

/-- CompPoly's `leeOSullivanInterpolate`, with `normalizeLeeFast`. -/
@[expose] def leeOSullivanInterpolateFast {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (reducer : PolynomialMatrix.ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) : Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    leeOSullivanPositiveInterpolateFast V E reducer points params

theorem leeOSullivanInterpolateFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (reducer : PolynomialMatrix.ShiftedRowReducerContext F) :
    leeOSullivanInterpolateFast V E reducer = LeeOSullivan.leeOSullivanInterpolate V E reducer := by
  funext points params
  unfold leeOSullivanInterpolateFast leeOSullivanPositiveInterpolateFast
    leeOSullivanPositiveCoreFast
  simp only [leeRowsFast_eq]
  rewrite [normalizeLeeFast_eq_fun]
  rfl

theorem gsInterpContext_ext {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    {A B : GSInterpContext F} (h : A.interpolate = B.interpolate) : A = B := by
  obtain ⟨f, _, _⟩ := A
  obtain ⟨g, _, _⟩ := B
  obtain rfl : f = g := h
  rfl

/-- CompPoly's `leeOSullivanInterpContext`, with `normalizeLeeFast`; its contracts CompPoly's,
transported. -/
@[expose] def leeOSullivanInterpContextFast {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (reducer : PolynomialMatrix.ShiftedRowReducerContext F) :
    GSInterpContext F where
  interpolate := leeOSullivanInterpolateFast V E reducer
  sound points params Q h := by
    have e := congrFun (congrFun (leeOSullivanInterpolateFast_eq V E reducer) points) params
    exact (LeeOSullivan.leeOSullivanInterpContext V E reducer).sound points params Q (e.symm.trans h)
  complete points params hd hex := by
    have e := congrFun (congrFun (leeOSullivanInterpolateFast_eq V E reducer) points) params
    obtain ⟨Q, hQ⟩ :=
      (LeeOSullivan.leeOSullivanInterpContext V E reducer).complete points params hd hex
    exact ⟨Q, e.trans hQ⟩

theorem leeOSullivanInterpContextFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (reducer : PolynomialMatrix.ShiftedRowReducerContext F) :
    leeOSullivanInterpContextFast V E reducer = LeeOSullivan.leeOSullivanInterpContext V E reducer :=
  gsInterpContext_ext (leeOSullivanInterpolateFast_eq V E reducer)

/-! ## Monic remainders without the quotient -/

theorem rawModContext_ext {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {A B : CPolynomial.Raw.ModContext F} (h : A.modByMonic = B.modByMonic) : A = B := by
  obtain ⟨f, _⟩ := A
  obtain ⟨g, _⟩ := B
  obtain rfl : f = g := h
  rfl

/-- CompPoly's remainder-only raw context is its naive one (`modByMonic` through
`divModByMonicAux`): the two remainders agree on every input. -/
theorem rawModContext_remainderOnly_eq_naive {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    (CPolynomial.Raw.ModContext.remainderOnly : CPolynomial.Raw.ModContext F) =
      CPolynomial.Raw.ModContext.naive := by
  apply rawModContext_ext
  funext p q
  exact CPolynomial.Raw.modByMonicRemainderOnly_eq_modByMonic p q

theorem fieldRootContext_ext {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {A B : FieldRootContext F} (h : A.rootsInField = B.rootsInField) : A = B := by
  obtain ⟨f, _, _⟩ := A
  obtain ⟨g, _, _⟩ := B
  obtain rfl : f = g := h
  rfl

/-! ## The Euclidean gcd with remainder-only division

`CPolynomial.Raw.gcdMonicWithFuel` reduces with `p % q` (`CPolynomial.Raw.mod`: the monic
`modByMonic`, through `divModByMonicAux`), not through a `ModContext`; it is called by the root
product (`finiteFieldRootProductWith`) and, as `CPolynomial.gcdMonic`, by Shoup's splitter. -/

/-- `p % q` (`CPolynomial.Raw.mod`) with the remainder-only long division. -/
@[expose] def rawModFast {F : Type*} [Field F] [BEq F] (p q : CPolynomial.Raw F) :
    CPolynomial.Raw F :=
  CPolynomial.Raw.modByMonicRemainderOnly (CPolynomial.Raw.C (q.leadingCoeff)⁻¹ • p)
    (CPolynomial.Raw.C (q.leadingCoeff)⁻¹ * q)

theorem rawModFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] (p q : CPolynomial.Raw F) :
    rawModFast p q = p % q := by
  rewrite [rawModFast, CPolynomial.Raw.modByMonicRemainderOnly_eq_modByMonic]
  rfl

/-- CompPoly's `CPolynomial.Raw.gcdMonicWithFuel`, with `rawModFast`. -/
@[expose] def rawGcdMonicWithFuelFast {F : Type*} [Field F] [BEq F] :
    ℕ → CPolynomial.Raw F → CPolynomial.Raw F → CPolynomial.Raw F
  | 0, p, _ => CPolynomial.Raw.monicNormalize p
  | fuel + 1, p, q =>
      let p := p.trim
      let q := q.trim
      if q == 0 then
        CPolynomial.Raw.monicNormalize p
      else
        rawGcdMonicWithFuelFast fuel q (rawModFast p q)

theorem rawGcdMonicWithFuelFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] (fuel : ℕ)
    (p q : CPolynomial.Raw F) :
    rawGcdMonicWithFuelFast fuel p q = CPolynomial.Raw.gcdMonicWithFuel fuel p q := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [rawGcdMonicWithFuelFast, CPolynomial.Raw.gcdMonicWithFuel, ih, rawModFast_eq]

/-- CompPoly's `CPolynomial.Raw.gcdMonic`, with `rawModFast`. -/
@[expose] def rawGcdMonicFast {F : Type*} [Field F] [BEq F] (p q : CPolynomial.Raw F) :
    CPolynomial.Raw F :=
  rawGcdMonicWithFuelFast (p.size + q.size + 1) p q

theorem rawGcdMonicFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p q : CPolynomial.Raw F) : rawGcdMonicFast p q = CPolynomial.Raw.gcdMonic p q :=
  rawGcdMonicWithFuelFast_eq (p.size + q.size + 1) p q

/-- CompPoly's `CPolynomial.gcdMonic`, with `rawModFast`. -/
@[expose] def gcdMonicFast {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p q : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (rawGcdMonicFast p.val q.val)

theorem gcdMonicFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] (p q : CPolynomial F) :
    gcdMonicFast p q = CPolynomial.gcdMonic p q := by
  rewrite [gcdMonicFast, rawGcdMonicFast_eq]
  rfl

/-! ## The vanishing polynomial, the short factor first -/

/-- CompPoly's `vanishingPolynomialArray` (`∏ (X − x)`), each product `(X − x) * acc`: the
schoolbook product folds over its first operand, here of two coefficients. -/
@[expose] def vanishingFast {F : Type*} [Field F] [BEq F] [LawfulBEq F] (xs : Array F) :
    CPolynomial F :=
  xs.foldl (fun acc x ↦ CPolynomial.linearFactor x * acc) 1

theorem vanishingFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] (xs : Array F) :
    vanishingFast xs = CPolynomial.vanishingPolynomialArray xs := by
  unfold vanishingFast CPolynomial.vanishingPolynomialArray
  congr 1
  funext acc x
  exact CPolynomial.mul_comm _ _

/-- The vanishing-polynomial context of `vanishingFast`. -/
@[expose] def vanishingContextFast {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial.VanishingPolynomialContext F where
  vanishingPolynomial := vanishingFast
  correct := vanishingFast_eq

theorem vanishingContext_ext {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {A B : CPolynomial.VanishingPolynomialContext F}
    (h : A.vanishingPolynomial = B.vanishingPolynomial) : A = B := by
  obtain ⟨f, _⟩ := A
  obtain ⟨g, _⟩ := B
  obtain rfl : f = g := h
  rfl

theorem vanishingContextFast_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    (vanishingContextFast : CPolynomial.VanishingPolynomialContext F) =
      CPolynomial.VanishingPolynomialContext.direct :=
  vanishingContext_ext (funext vanishingFast_eq)

/-! ## The decoder's interpolation -/

/-- **The decoder's interpolation, fast**: `interpContext` (`Fast/Extract.lean`) with
`vanishingContextFast` and `normalizeLeeFast`. -/
@[expose] def interpContextFast : GSInterpContext K :=
  leeOSullivanInterpContextFast vanishingContextFast (CPolynomial.BatchEvalContext.horner K)
    (PolynomialMatrix.muldersStorjohannFastReducerContext K)

/-- `interpContextFast` is `interpContext`'s body (`interpContext` unfolds to the right side). -/
theorem interpContextFast_eq : interpContextFast =
    LeeOSullivan.leeOSullivanInterpContext CPolynomial.VanishingPolynomialContext.direct
      (CPolynomial.BatchEvalContext.horner K)
      (PolynomialMatrix.muldersStorjohannFastReducerContext K) := by
  rw [interpContextFast, leeOSullivanInterpContextFast_eq, vanishingContextFast_eq]

/-! ## The interpolation of distinct points

The lane decoder's points are distinct (`distinct_lanePoints`, `Fast/Extract.lean`), so the
distinctness check (`distinctXCoordinatesBool`: each point compared with every later one, `n²/2`
comparisons) is skipped there. -/

/-- `interpContextFast`'s interpolation without the distinctness check. -/
@[expose] def interpolateDistinct (points : Array (K × K)) (params : GSInterpParams) :
    Option (CBivariate K) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    leeOSullivanPositiveCoreFast vanishingContextFast (CPolynomial.BatchEvalContext.horner K)
      (PolynomialMatrix.muldersStorjohannFastReducerContext K) points params

/-- On distinct points, `interpolateDistinct` is `interpContextFast`'s interpolation. -/
theorem interpolateDistinct_eq {points : Array (K × K)} (h : DistinctXCoordinates points)
    (params : GSInterpParams) :
    interpolateDistinct points params = interpContextFast.interpolate points params := by
  show _ = leeOSullivanInterpolateFast _ _ _ points params
  rw [interpolateDistinct, leeOSullivanInterpolateFast, leeOSullivanPositiveInterpolateFast,
    LeeOSullivan.distinctXCoordinatesBool_iff.2 h]
  rfl

/-! ## Evaluation by Horner's rule

CompPoly's `CPolynomial.eval x p` sums `a_i·x^i`, each power computed anew (`log i` products
by squaring); Horner's rule takes one product and one sum per coefficient. -/

/-- `p(x)` by Horner's rule. -/
@[expose] def hornerEval {F : Type*} [Semiring F] (x : F) (p : CPolynomial F) : F :=
  p.val.foldr (fun a acc ↦ acc * x + a) 0

theorem hornerEval_eq {F : Type*} [Semiring F] (x : F) (p : CPolynomial F) :
    hornerEval x p = CPolynomial.eval x p :=
  CPolynomial.eval_horner_eq_eval x p

theorem hornerEval_eq_fun {F : Type*} [Semiring F] :
    (hornerEval : F → CPolynomial F → F) = CPolynomial.eval := by
  funext x p
  exact hornerEval_eq x p

/-- CompPoly's `candidateMismatchCount` with `hornerEval`. -/
@[expose] def mismatchCountFast {F : Type*} [Semiring F] [BEq F] (points : Array (F × F))
    (p : CPolynomial F) : ℕ :=
  points.foldl (fun count point ↦ if hornerEval point.1 p == point.2 then count else count + 1) 0

/-- CompPoly's `passesCandidateDistance` with `hornerEval`. -/
@[expose] def passesDistanceFast {F : Type*} [Semiring F] [BEq F] (points : Array (F × F))
    (radius : ℕ) (p : CPolynomial F) : Bool :=
  decide (mismatchCountFast points p ≤ radius)

theorem passesDistanceFast_eq {F : Type*} [Semiring F] [BEq F] :
    (passesDistanceFast : Array (F × F) → ℕ → CPolynomial F → Bool) =
      passesCandidateDistance := by
  funext points radius p
  rw [passesDistanceFast, mismatchCountFast, hornerEval_eq_fun]
  rfl

/-- The statement's `toNovel` with `hornerEval`. -/
@[expose] def toNovelFast (κ : ℕ) (p : CPolynomial K) : Array K :=
  LeanVM.Extraction.novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ hornerEval (K.ofBits v.val) p)

theorem toNovelFast_eq : toNovelFast = LeanVM.Extraction.toNovel := by
  funext κ p
  rw [toNovelFast, hornerEval_eq_fun]
  rfl

end

end LeanVM.Extraction.Fast
