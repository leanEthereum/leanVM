module

public import LeanVM.Protocol.Extraction.Fast.EvalMat.Transform
public import CompPoly.LinearAlgebra.PolynomialMatrix.StrassenCorrectness

/-!
# Polynomial-matrix products in the evaluation domain

`mulEval T mulCtx A B`, for `A` of `r` rows and `B` of `s` rows and `t` columns: one size `2^j`
for the whole product, the least with `deg A + deg B < 2^j` (`deg` the largest entry degree);
the `r·s` entries of `A` and the `s·t` of `B` transformed once each (`transformEntries`), at each
of the `2^j` points the `r·t` sums of `s` products (`evalDot`), and one inverse transform per
output entry. Above the transform's sizes, the schoolbook product (`mulWith mulCtx`).

`mulTruncEval T mulCtx orders A B` keeps the coefficients of column `c` below `orders[c]`: the
inputs truncated first at the largest order `O` (a coefficient below `O` of a product reads only
coefficients below `O`), so `j` the least with `min(deg A, O − 1) + min(deg B, O − 1) < 2^j`.

**`mulEval_eq_mulWith`** and **`mulTruncEval_eq_truncateColumns`**: they are CompPoly's naive
products, as arrays; hence CompPoly's Strassen products (`mulEval_eq_mulStrassenWith`,
`mulTruncEval_eq_mulTruncColumnStrassenWith`), whatever their contexts and cutoffs.

K-operations (`N = 2^j`, `C(N)` a transform's cost): `(r·s + s·t)·C_fwd(N) + r·t·C_inv(N)`
transforms and `r·s·t·N` multiplications and additions pointwise.
-/

namespace LeanVM.Extraction.Fast.EvalMat

open CompPoly PolynomialMatrix

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ### Folds of maxima -/

theorem le_foldl_of_le {α : Type*} (g : ℕ → α → ℕ) (hg : ∀ a x, a ≤ g a x) :
    ∀ (l : List α) (a : ℕ), a ≤ l.foldl g a
  | [], _ => le_rfl
  | x :: l, a => (hg a x).trans (le_foldl_of_le g hg l (g a x))

theorem le_foldl_of_mem {α : Type*} (g : ℕ → α → ℕ) (hg : ∀ a x, a ≤ g a x) (b : ℕ) (x : α)
    (hx : ∀ a, b ≤ g a x) : ∀ (l : List α) (a : ℕ), x ∈ l → b ≤ l.foldl g a
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, a, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (hx a).trans (le_foldl_of_le g hg l _)
    · exact le_foldl_of_mem g hg b x hx l _ h

omit [BEq F] [LawfulBEq F] in
/-- The largest degree of the entries `(i, k)`, `i < rows`, `k < cols`, of `M`. -/
@[expose] def maxEntryDegree (M : PolynomialMatrix F) (rows cols : ℕ) : ℕ :=
  (List.range rows).foldl
    (fun acc i ↦ (List.range cols).foldl
      (fun acc k ↦ max acc (rowGet (M.getD i #[]) k).natDegree) acc) 0

omit [BEq F] [LawfulBEq F] in
theorem natDegree_le_maxEntryDegree (M : PolynomialMatrix F) {rows cols i k : ℕ}
    (hi : i < rows) (hk : k < cols) :
    (rowGet (M.getD i #[]) k).natDegree ≤ maxEntryDegree M rows cols := by
  have hinner : ∀ i, ∀ a x, a ≤ (fun acc k ↦ max acc (rowGet (M.getD i #[]) k).natDegree) a x :=
    fun _ _ _ ↦ le_max_left _ _
  refine le_foldl_of_mem _ (fun a i ↦ le_foldl_of_le _ (hinner i) _ a) _ i (fun a ↦ ?_) _ _
    (List.mem_range.mpr hi)
  exact le_foldl_of_mem _ (hinner i) _ k (fun _ ↦ le_max_right _ _) _ _ (List.mem_range.mpr hk)

/-- The largest of `orders[c]`, `c < cols`. -/
@[expose] def maxOrderOf (orders : Array ℕ) (cols : ℕ) : ℕ :=
  (List.range cols).foldl (fun acc c ↦ max acc (orders.getD c 0)) 0

theorem getD_le_maxOrderOf (orders : Array ℕ) {cols c : ℕ} (hc : c < cols) :
    orders.getD c 0 ≤ maxOrderOf orders cols :=
  le_foldl_of_mem (fun acc c ↦ max acc (orders.getD c 0)) (fun _ _ ↦ le_max_left _ _) _ c (fun _ ↦ le_max_right _ _) _ _
    (List.mem_range.mpr hc)

/-! ### The size -/

/-- The search for the least `j ≥ j₀` with `e ≤ 2^j`, `fuel` steps at most. -/
@[expose] def ceilLogLoop (e : ℕ) : ℕ → ℕ → ℕ
  | 0, j => j
  | fuel + 1, j => if e ≤ 2 ^ j then j else ceilLogLoop e fuel (j + 1)

/-- `⌈log₂ e⌉`: the least `j` with `e ≤ 2^j`. -/
@[expose] def ceilLog (e : ℕ) : ℕ := ceilLogLoop e e 0

theorem le_two_pow_ceilLogLoop (e : ℕ) :
    ∀ fuel j, e ≤ j + fuel → e ≤ 2 ^ ceilLogLoop e fuel j
  | 0, j, h => by
    rw [ceilLogLoop]
    exact (Nat.le_of_lt_succ (by omega : e < j + 1)).trans (Nat.lt_two_pow_self).le
  | fuel + 1, j, h => by
    rw [ceilLogLoop]
    split
    · assumption
    · exact le_two_pow_ceilLogLoop e fuel (j + 1) (by omega)

theorem le_two_pow_ceilLog (e : ℕ) : e ≤ 2 ^ ceilLog e :=
  le_two_pow_ceilLogLoop e e 0 (by omega)

theorem ceilLogLoop_le (e : ℕ) {j : ℕ} (hj : e ≤ 2 ^ j) :
    ∀ fuel j₀, j₀ ≤ j → ceilLogLoop e fuel j₀ ≤ j
  | 0, _, h => h
  | fuel + 1, j₀, h => by
    rw [ceilLogLoop]
    split
    · exact h
    · rename_i hlt
      have : j₀ < j := by
        by_contra hc
        exact hlt (hj.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      exact ceilLogLoop_le e hj fuel (j₀ + 1) this

/-- `ceilLog e` is the least: `e ≤ 2^j` gives `ceilLog e ≤ j`. -/
theorem ceilLog_le {e j : ℕ} (hj : e ≤ 2 ^ j) : ceilLog e ≤ j :=
  ceilLogLoop_le e hj e 0 (Nat.zero_le _)

/-! ### The transforms and the pointwise products -/

/-- The transforms of size `2^j` of the entries `entry i k`, `i < rows`, `k < cols`. -/
@[expose] def transformEntries (T : EvalTransform F) (j rows cols : ℕ)
    (entry : ℕ → ℕ → CPolynomial F) : Array (Array (Array F)) :=
  Array.ofFn fun i : Fin rows ↦ Array.ofFn fun k : Fin cols ↦ T.fwd j (entry i k)

theorem transformEntries_getD (T : EvalTransform F) (j : ℕ) {rows cols : ℕ}
    (entry : ℕ → ℕ → CPolynomial F) {i k : ℕ} (hi : i < rows) (hk : k < cols) :
    ((transformEntries T j rows cols entry).getD i #[]).getD k #[] = T.fwd j (entry i k) := by
  simp only [transformEntries, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, hk,
    dite_true, Option.getD_some]

/-- At each of the `N` points, `Σ_{k<s} a[k] · B[k][c]`: row `a` of the left factor's
transforms against column `c` of the right factor's. -/
@[expose] def evalDot (N s : ℕ) (a : Array (Array F)) (B : Array (Array (Array F))) (c : ℕ) :
    Array F :=
  Array.ofFn fun v : Fin N ↦
    (List.range s).foldl
      (fun acc k ↦ acc + (a.getD k #[]).getD v 0 * ((B.getD k #[]).getD c #[]).getD v 0) 0

/-- Entry `(i, c)` of the evaluation-domain product: the inverse transform of `evalDot`. -/
@[expose] def evalEntry (T : EvalTransform F) (j s : ℕ) (FA FB : Array (Array (Array F)))
    (i c : ℕ) : CPolynomial F :=
  T.inv j (evalDot (2 ^ j) s (FA.getD i #[]) FB c)

theorem evalEntry_eq (T : EvalTransform F) {j : ℕ} (hj : j ≤ T.maxLog) {rows s cols : ℕ}
    (f g : ℕ → ℕ → CPolynomial F) {d₁ d₂ : ℕ}
    (hf : ∀ i < rows, ∀ k < s, (f i k).natDegree ≤ d₁)
    (hg : ∀ k < s, ∀ c < cols, (g k c).natDegree ≤ d₂) (hd : d₁ + d₂ < 2 ^ j)
    {i c : ℕ} (hi : i < rows) (hc : c < cols) :
    evalEntry T j s (transformEntries T j rows s f) (transformEntries T j s cols g) i c =
      ∑ k ∈ Finset.range s, f i k * g k c := by
  rw [← T.inv_sum_mul hj s (fun k ↦ f i k) (fun k ↦ g k c) (fun k hk ↦ hf i hi k hk)
    (fun k hk ↦ hg k hk c hc) hd, evalEntry, evalDot]
  refine congrArg (T.inv j) (congrArg Array.ofFn (funext fun v ↦ ?_))
  rw [EvalTransform.foldl_range_add, EvalTransform.foldl_range_add]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.mp hk
  rw [transformEntries_getD T j f hi hk, transformEntries_getD T j g hk hc]

/-- **The evaluation-domain product** of the `rows × s` matrix `f` and the `s × cols` matrix
`g` at size `2^j`. -/
@[expose] def evalProduct (T : EvalTransform F) (j rows s cols : ℕ)
    (f g : ℕ → ℕ → CPolynomial F) : PolynomialMatrix F :=
  let FA := transformEntries T j rows s f
  let FB := transformEntries T j s cols g
  ofFn rows cols fun i c ↦ evalEntry T j s FA FB i c

theorem evalProduct_eq (T : EvalTransform F) {j : ℕ} (hj : j ≤ T.maxLog) {rows s cols : ℕ}
    (f g : ℕ → ℕ → CPolynomial F) {d₁ d₂ : ℕ}
    (hf : ∀ i < rows, ∀ k < s, (f i k).natDegree ≤ d₁)
    (hg : ∀ k < s, ∀ c < cols, (g k c).natDegree ≤ d₂) (hd : d₁ + d₂ < 2 ^ j) :
    evalProduct T j rows s cols f g =
      ofFn rows cols fun i c ↦ ∑ k ∈ Finset.range s, f i k * g k c :=
  ofFn_congr fun _ hi _ hc ↦ evalEntry_eq T hj f g hf hg hd hi hc

/-! ### The product -/

/-- **The polynomial-matrix product in the evaluation domain**, `A · B`. -/
@[expose] def mulEval (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  let r := A.size
  let s := B.size
  let t := MatrixWidth B
  let j := ceilLog (maxEntryDegree A r s + maxEntryDegree B s t + 1)
  if j ≤ T.maxLog then
    evalProduct T j r s t (fun i k ↦ rowGet (A.getD i #[]) k) (fun k c ↦ rowGet (B.getD k #[]) c)
  else mulWith mulCtx A B

/-- **`mulEval` is the naive product** (of any context). -/
theorem mulEval_eq_mulWith (T : EvalTransform F) (mulCtx mulCtx' : CPolynomial.MulContext F)
    (A B : PolynomialMatrix F) : mulEval T mulCtx A B = mulWith mulCtx' A B := by
  rw [mulEval]
  split
  · rename_i hj
    rw [mulWith_eq_ofFn]
    exact evalProduct_eq T hj _ _ (fun i hi k hk ↦ natDegree_le_maxEntryDegree A hi hk)
      (fun k hk c hc ↦ natDegree_le_maxEntryDegree B hk hc)
      (Nat.lt_of_succ_le (le_two_pow_ceilLog _))
  · rw [mulWith_eq_ofFn, mulWith_eq_ofFn]

/-- **`mulEval` is CompPoly's Strassen product**, whatever its context and cutoff. -/
theorem mulEval_eq_mulStrassenWith (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff : ℕ) (A B : PolynomialMatrix F) :
    mulEval T mulCtx A B = mulStrassenWith lowCtx leafCutoff A B := by
  rw [mulStrassenWith_eq_mulWith, mulEval_eq_mulWith]

/-! ### The column-truncated product -/

theorem natDegree_truncateX_le (O : ℕ) (p : CPolynomial F) :
    (truncateX O p).natDegree ≤ min p.natDegree (O - 1) := by
  rw [CPolynomial.natDegree_toPoly, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [← CPolynomial.coeff_toPoly, truncateX_coeff]
  split
  · rename_i hiO
    rw [CPolynomial.coeff_toPoly]
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    rw [← CPolynomial.natDegree_toPoly]
    have : p.natDegree < i ∨ O - 1 < i := by
      rcases le_total p.natDegree (O - 1) with h | h
      · left; rw [min_eq_left h] at hi; exact_mod_cast hi
      · right; rw [min_eq_right h] at hi; exact_mod_cast hi
    omega
  · rfl

/-- A coefficient below `o ≤ O` of a product reads only coefficients below `O`. -/
theorem truncateX_mul_truncateX {o O : ℕ} (hoO : o ≤ O) (p q : CPolynomial F) :
    truncateX o (truncateX O p * truncateX O q) = truncateX o (p * q) := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  rw [truncateX_coeff, truncateX_coeff]
  split
  · rw [CPolynomial.coeff_mul, CPolynomial.coeff_mul]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk := Finset.mem_range.mp hk
    simp only [truncateX_coeff, show k < O by omega, show i - k < O by omega, ↓reduceIte]
  · rfl

/-- **The column-truncated product in the evaluation domain**: column `c` of `A · B` below
`orders[c]`. -/
@[expose] def mulTruncEval (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (orders : Array ℕ) (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  let r := A.size
  let s := B.size
  let t := MatrixWidth B
  let O := maxOrderOf orders t
  let j := ceilLog (min (maxEntryDegree A r s) (O - 1) + min (maxEntryDegree B s t) (O - 1) + 1)
  if j ≤ T.maxLog then
    let FA := transformEntries T j r s fun i k ↦ truncateX O (rowGet (A.getD i #[]) k)
    let FB := transformEntries T j s t fun k c ↦ truncateX O (rowGet (B.getD k #[]) c)
    ofFn r t fun i c ↦ truncateX (orders.getD c 0) (evalEntry T j s FA FB i c)
  else truncateColumns orders (mulWith mulCtx A B)

/-- **`mulTruncEval` is the truncated naive product** (of any context). -/
theorem mulTruncEval_eq_truncateColumns (T : EvalTransform F)
    (mulCtx mulCtx' : CPolynomial.MulContext F) (orders : Array ℕ) (A B : PolynomialMatrix F) :
    mulTruncEval T mulCtx orders A B = truncateColumns orders (mulWith mulCtx' A B) := by
  rw [mulTruncEval]
  split
  · rename_i hj
    rw [mulWith_eq_ofFn, truncateColumns_ofFn]
    refine ofFn_congr fun i hi c hc ↦ ?_
    rw [evalEntry_eq T hj _ _
      (d₁ := min (maxEntryDegree A A.size B.size) (maxOrderOf orders (MatrixWidth B) - 1))
      (d₂ := min (maxEntryDegree B B.size (MatrixWidth B)) (maxOrderOf orders (MatrixWidth B) - 1))
      (fun i hi k hk ↦ (natDegree_truncateX_le _ _).trans
        (min_le_min_right _ (natDegree_le_maxEntryDegree A hi hk)))
      (fun k hk c hc ↦ (natDegree_truncateX_le _ _).trans
        (min_le_min_right _ (natDegree_le_maxEntryDegree B hk hc)))
      (Nat.lt_of_succ_le (le_two_pow_ceilLog _)) hi hc,
      truncateX_sum, truncateX_sum]
    exact Finset.sum_congr rfl fun k _ ↦
      truncateX_mul_truncateX (getD_le_maxOrderOf orders hc) _ _
  · rw [mulWith_eq_ofFn, mulWith_eq_ofFn]

/-- **`mulTruncEval` is CompPoly's column-truncated Strassen product**, whatever its context and
cutoff. -/
theorem mulTruncEval_eq_mulTruncColumnStrassenWith (T : EvalTransform F)
    (mulCtx : CPolynomial.MulContext F) (lowCtx : MulLowContext F) (leafCutoff : ℕ)
    (orders : Array ℕ) (A B : PolynomialMatrix F) :
    mulTruncEval T mulCtx orders A B = mulTruncColumnStrassenWith lowCtx leafCutoff orders A B := by
  rw [mulTruncColumnStrassenWith_eq_truncateColumns, mulTruncEval_eq_truncateColumns]

end

end LeanVM.Extraction.Fast.EvalMat
