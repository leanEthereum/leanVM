module

public import CompPoly.Univariate.ToPoly
public import CompPoly.Univariate.Context
public import CompPoly.LinearAlgebra.PolynomialMatrix.Operations
public import LeanVM.Protocol.Extraction.Fast.EvalMat.Transform
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic

/-!
# Evaluation transforms and the products they give

A **point transform** (`PointTransform F`) evaluates a polynomial of at most `2^j`
coefficients on `2^j` points `point 0, …, point (2^j − 1)` (`fwd j`), and interpolates `2^j`
values back to the polynomial of at most `2^j` coefficients taking them (`inv j`), for every
`j ≤ maxLog`. Its laws are stated as evaluations, so a user needs no knowledge of the points:

* `fwd_getD`: entry `v < 2^j` of `fwd j p` is `p(point v)`;
* `inv_eq`: if `y_v = p(point v)` for `v < 2^j`, `inv j y = p` (so the points are distinct);
* `fwd_inv`, `size_inv`: every `2^j` values are taken by `inv j y`, of at most `2^j`
  coefficients.

Derived here: `inv_fwd` (interpolation inverts evaluation), `fwd_mul` (evaluation is pointwise
multiplicative below `2^j` coefficients), and the product through the
evaluation domain, `inv_pmul_fwd`: `inv j (fwd j p ⊙ fwd j q) = p·q` when `p·q` fits.

`mulVia T S`: CompPoly's product by the transform `T`, at the least `j` with `2^j` points for
`p·q`, schoolbook when a factor has at most `c` coefficients or `j > maxLog`; **`mulVia_eq`**:
it is `p * q`. Contexts for CompPoly: `mulContextOf` (`CPolynomial.MulContext`),
`mulLowContextOf` (`PolynomialMatrix.MulLowContext`: the truncated product as one product of the
truncated factors, not a full product per coefficient) and `rawMulLowContextOf`
(`CPolynomial.Raw.MulLowContext`, for `ModContext.reversal`).

`PointTransform.toEvalMat`: the interface of the evaluation-domain matrix products
(`EvalMat.EvalTransform`, laws below `2^j` coefficients by degree) from one. The novel-basis
transform over `K` (`Fast/FFT/Additive.lean`) is an instance.
-/

namespace LeanVM.Extraction.Fast.FFT

open CompPoly

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Sizes of canonical polynomials -/

omit [BEq F] [LawfulBEq F] in
/-- A canonical polynomial whose coefficients vanish from `n` on has at most `n` coefficients. -/
theorem size_le_of_coeff_eq_zero (p : CPolynomial F) {n : ℕ}
    (h : ∀ i, n ≤ i → p.coeff i = 0) : p.val.size ≤ n := by
  by_contra hlt
  have hpos : p.val.size > 0 := by omega
  apply p.property hpos
  have := h (p.val.size - 1) (by omega)
  simp only [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD,
    show p.val.size - 1 < p.val.size by omega, dite_true] at this
  simpa [Array.getLast] using this

/-- A product has at most `|p| + |q| − 1` coefficients. -/
theorem size_mul_le (p q : CPolynomial F) (hp : 0 < p.val.size) (hq : 0 < q.val.size) :
    (p * q).val.size ≤ p.val.size + q.val.size - 1 := by
  apply size_le_of_coeff_eq_zero
  intro k hk
  rw [CPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hi := Finset.mem_range.mp hi
  by_cases h : p.val.size ≤ i
  · rw [CPolynomial.coeff_eq_zero_of_size_le _ h, zero_mul]
  · rw [CPolynomial.coeff_eq_zero_of_size_le q (by omega), mul_zero]

/-- The coefficients below `k` of a product depend only on the factors' below `k`. -/
theorem coeff_mul_of_agree {p q p' q' : CPolynomial F} {k : ℕ}
    (hp : ∀ a < k, p'.coeff a = p.coeff a) (hq : ∀ a < k, q'.coeff a = q.coeff a)
    {i : ℕ} (hi : i < k) : (p' * q').coeff i = (p * q).coeff i := by
  rw [CPolynomial.coeff_mul, CPolynomial.coeff_mul]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha := Finset.mem_range.mp ha
  rw [hp a (by omega), hq (i - a) (by omega)]

/-! ## Pointwise products -/

/-- The pointwise product of the first `n` entries. -/
@[expose] def pmul (n : ℕ) (a b : Array F) : Array F :=
  Array.ofFn fun v : Fin n ↦ a.getD v.val 0 * b.getD v.val 0

omit [BEq F] [LawfulBEq F] in
theorem getD_ofFn' {n p : ℕ} (f : Fin n → F) (hp : p < n) :
    (Array.ofFn f).getD p 0 = f ⟨p, hp⟩ := by
  simp [Array.getD, hp]

omit [BEq F] [LawfulBEq F] in
theorem array_ext_getD' {a b : Array F} (h : a.size = b.size)
    (hg : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  apply Array.ext h
  intro p h1 h2
  have := hg p h1
  simp only [Array.getD, h1, h2, dite_true] at this
  exact this

/-! ## The transforms -/

/-- **A point transform** on `2^j` points, `j ≤ maxLog`: `fwd j` evaluates a polynomial of at
most `2^j` coefficients at `point 0, …, point (2^j − 1)`, `inv j` interpolates. Both go through a
**plan** (`plan j : Plan`, the precomputations of size `2^j`): `fwd j = fwdP (plan j)`, so a
caller transforming many polynomials of one size builds the plan once (`fwdP P`, `invP P`). -/
structure PointTransform (F : Type*) [Field F] [BEq F] [LawfulBEq F] (Plan : Type) where
  /-- The largest `j` the laws hold at. -/
  maxLog : ℕ
  /-- The evaluation points. -/
  point : ℕ → F
  /-- The precomputations of size `2^j`. -/
  plan : ℕ → Plan
  /-- The evaluations on `2^j` points, by the plan of size `2^j`. -/
  fwdP : Plan → CPolynomial F → Array F
  /-- The interpolation from `2^j` values, by the plan of size `2^j`. -/
  invP : Plan → Array F → CPolynomial F
  size_fwd : ∀ {j : ℕ} (p : CPolynomial F), j ≤ maxLog → (fwdP (plan j) p).size = 2 ^ j
  /-- `fwd` evaluates. -/
  fwd_getD : ∀ {j : ℕ} (p : CPolynomial F), j ≤ maxLog → p.val.size ≤ 2 ^ j →
    ∀ {v : ℕ}, v < 2 ^ j → (fwdP (plan j) p).getD v 0 = p.eval (point v)
  /-- `inv` interpolates: the polynomial of at most `2^j` coefficients with the values. -/
  inv_eq : ∀ {j : ℕ} (y : Array F) (p : CPolynomial F), j ≤ maxLog → y.size = 2 ^ j →
    p.val.size ≤ 2 ^ j → (∀ v < 2 ^ j, y.getD v 0 = p.eval (point v)) → invP (plan j) y = p
  size_inv : ∀ {j : ℕ} (y : Array F), j ≤ maxLog → y.size = 2 ^ j →
    (invP (plan j) y).val.size ≤ 2 ^ j
  /-- Every `2^j` values are interpolated. -/
  fwd_inv : ∀ {j : ℕ} (y : Array F), j ≤ maxLog → y.size = 2 ^ j →
    fwdP (plan j) (invP (plan j) y) = y

variable {Plan : Type}

namespace PointTransform

/-- The evaluations on `2^j` points. -/
abbrev fwd (T : PointTransform F Plan) (j : ℕ) : CPolynomial F → Array F := T.fwdP (T.plan j)

/-- The interpolation from `2^j` values. -/
abbrev inv (T : PointTransform F Plan) (j : ℕ) : Array F → CPolynomial F := T.invP (T.plan j)

end PointTransform

namespace PointTransform

variable (T : PointTransform F Plan)

/-- **Interpolation inverts evaluation.** -/
theorem inv_fwd {j : ℕ} (hj : j ≤ T.maxLog) (p : CPolynomial F) (hp : p.val.size ≤ 2 ^ j) :
    T.inv j (T.fwd j p) = p :=
  T.inv_eq _ p hj (T.size_fwd p hj) hp fun _ hv ↦ T.fwd_getD p hj hp hv

/-- **Evaluation is multiplicative** when the product fits. -/
theorem fwd_mul {j : ℕ} (hj : j ≤ T.maxLog) (p q : CPolynomial F) (hp : p.val.size ≤ 2 ^ j)
    (hq : q.val.size ≤ 2 ^ j) (hpq : (p * q).val.size ≤ 2 ^ j) :
    T.fwd j (p * q) = pmul (2 ^ j) (T.fwd j p) (T.fwd j q) := by
  apply array_ext_getD' (by rw [T.size_fwd _ hj, pmul, Array.size_ofFn])
  intro v hv
  rw [T.size_fwd _ hj] at hv
  rw [pmul, getD_ofFn' _ hv, T.fwd_getD _ hj hpq hv, T.fwd_getD _ hj hp hv, T.fwd_getD _ hj hq hv,
    CPolynomial.eval_mul]

/-- **The product through the evaluation domain.** -/
theorem inv_pmul_fwd {j : ℕ} (hj : j ≤ T.maxLog) (p q : CPolynomial F) (hp : p.val.size ≤ 2 ^ j)
    (hq : q.val.size ≤ 2 ^ j) (hpq : (p * q).val.size ≤ 2 ^ j) :
    T.inv j (pmul (2 ^ j) (T.fwd j p) (T.fwd j q)) = p * q := by
  rw [← T.fwd_mul hj p q hp hq hpq, T.inv_fwd hj _ hpq]

end PointTransform

omit [BEq F] [LawfulBEq F] in
/-- A canonical polynomial has at most `natDegree + 1` coefficients. -/
theorem size_le_natDegree_succ (p : CPolynomial F) : p.val.size ≤ p.natDegree + 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

namespace PointTransform

/-- **The evaluation-domain interface** (`EvalMat.EvalTransform`) of a point transform, at the
points `point j v = T.point v`. -/
@[expose] def toEvalMat (T : PointTransform F Plan) : EvalMat.EvalTransform F where
  maxLog := T.maxLog
  point _ v := T.point v
  fwd := T.fwd
  inv := T.inv
  size_fwd _ p hj _ := T.size_fwd p hj
  fwd_getD _ p hj hp _ hv :=
    T.fwd_getD p hj (le_trans (size_le_natDegree_succ p) (by omega)) hv
  inv_fwd _ p hj hp := T.inv_fwd hj p (le_trans (size_le_natDegree_succ p) (by omega))

end PointTransform

/-! ## The product -/

/-- A `j` with `2^j > n`, the least one. -/
@[expose] def logAbove (n : ℕ) : ℕ := Nat.log2 n + 1

theorem lt_two_pow_logAbove (n : ℕ) : n < 2 ^ logAbove n := Nat.lt_log2_self

/-- When to use the transform: the schoolbook product when a factor has at most `small`
coefficients (`≤ small·n` products, folding over the small factor), the `fallback` context's when
both have at most `mid`. -/
structure MulSchedule (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  small : ℕ
  mid : ℕ
  fallback : CPolynomial.MulContext F

/-- **The product by a point transform**: by the schedule `S` for small factors, else on `2^j`
points, `j` least with `2^j ≥ |p| + |q| − 1`, if `j ≤ maxLog` (else `S.fallback`). -/
@[expose] def mulVia (T : PointTransform F Plan) (S : MulSchedule F) (p q : CPolynomial F) :
    CPolynomial F :=
  if q.val.size ≤ S.small then q * p
  else if p.val.size ≤ S.small then p * q
  else if p.val.size ≤ S.mid ∧ q.val.size ≤ S.mid then S.fallback.mul p q
  else
    let j := logAbove (p.val.size + q.val.size - 2)
    if j ≤ T.maxLog then
      let P := T.plan j
      T.invP P (pmul (2 ^ j) (T.fwdP P p) (T.fwdP P q))
    else S.fallback.mul p q

/-- **The transform's product is CompPoly's.** -/
theorem mulVia_eq (T : PointTransform F Plan) (S : MulSchedule F) (p q : CPolynomial F) :
    mulVia T S p q = p * q := by
  unfold mulVia
  split
  · exact mul_comm q p
  split
  · rfl
  · rename_i hc' hc
    split
    · exact S.fallback.mul_eq_mul p q
    · dsimp only
      split
      · rename_i hj
        have h2 := lt_two_pow_logAbove (p.val.size + q.val.size - 2)
        have hpq := size_mul_le p q (by omega) (by omega)
        exact T.inv_pmul_fwd hj p q (by omega) (by omega) (by omega)
      · exact S.fallback.mul_eq_mul p q

/-- CompPoly's multiplication context for the transform's product. -/
@[expose] def mulContextOf (T : PointTransform F Plan) (S : MulSchedule F) : CPolynomial.MulContext F where
  mul := mulVia T S
  mul_eq_mul := mulVia_eq T S

/-- **The truncated product**: the low `order` coefficients of `p·q`, as the truncation of one
product of the truncated factors (at most `2·order − 1` coefficients). -/
@[expose] def mulLowVia (T : PointTransform F Plan) (S : MulSchedule F) (order : ℕ) (p q : CPolynomial F) :
    CPolynomial F :=
  PolynomialMatrix.truncateX order
    (mulVia T S (PolynomialMatrix.truncateX order p) (PolynomialMatrix.truncateX order q))

theorem mulLowVia_eq (T : PointTransform F Plan) (S : MulSchedule F) (order : ℕ) (p q : CPolynomial F) :
    mulLowVia T S order p q = PolynomialMatrix.truncateX order (p * q) := by
  rw [mulLowVia, mulVia_eq]
  apply CPolynomial.eq_iff_coeff.2
  intro i
  rw [PolynomialMatrix.truncateX_coeff, PolynomialMatrix.truncateX_coeff]
  split
  · rename_i hi
    refine coeff_mul_of_agree (fun a ha ↦ ?_) (fun a ha ↦ ?_) hi <;>
      (rw [PolynomialMatrix.truncateX_coeff]; simp [ha])
  · rfl

/-- CompPoly's polynomial-matrix low-product context for the transform's product. -/
@[expose] def mulLowContextOf (T : PointTransform F Plan) (S : MulSchedule F) :
    PolynomialMatrix.MulLowContext F where
  mulContext := mulContextOf T S
  mulLow := mulLowVia T S
  mulLow_eq := mulLowVia_eq T S

/-- The low `k` coefficients of a product of raw polynomials, by the transform's product of the
truncated factors. -/
@[expose] def rawMulLowVia (T : PointTransform F Plan) (S : MulSchedule F) (k : ℕ) (p q : CPolynomial.Raw F) :
    CPolynomial.Raw F :=
  (mulVia T S (CPolynomial.ofArray (p.extract 0 k)) (CPolynomial.ofArray (q.extract 0 k))).val.extract
    0 k

theorem coeff_ofArray_extract (p : CPolynomial.Raw F) {k a : ℕ} (ha : a < k) :
    (CPolynomial.ofArray (p.extract 0 k)).coeff a = p.coeff a := by
  rw [CPolynomial.coeff_ofArray, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  simp only [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Nat.zero_add]
  by_cases h : a < min k p.size
  · simp [h]
  · have : p.size ≤ a := by omega
    simp [h, Array.getElem?_eq_none this]

theorem coeff_rawMulLowVia (T : PointTransform F Plan) (S : MulSchedule F) (k : ℕ) (p q : CPolynomial.Raw F) (i : ℕ)
    (hi : i < k) : (rawMulLowVia T S k p q).coeff i = (p * q).coeff i := by
  have hext : (rawMulLowVia T S k p q).coeff i =
      (CPolynomial.ofArray (p.extract 0 k) * CPolynomial.ofArray (q.extract 0 k)).coeff i := by
    rw [rawMulLowVia, mulVia_eq]
    simp only [CPolynomial.Raw.coeff, CPolynomial.coeff, Array.getD_eq_getD_getElem?,
      Array.getElem?_extract]
    by_cases h : i < min k (CPolynomial.ofArray (p.extract 0 k) *
        CPolynomial.ofArray (q.extract 0 k)).val.size
    · simp [h]
    · have : (CPolynomial.ofArray (p.extract 0 k) *
          CPolynomial.ofArray (q.extract 0 k)).val.size ≤ i := by omega
      simp [h, Array.getElem?_eq_none this]
  rw [hext, CPolynomial.coeff_mul, CPolynomial.Raw.mul_coeff]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha := Finset.mem_range.mp ha
  rw [coeff_ofArray_extract p (by omega), coeff_ofArray_extract q (by omega)]

/-- CompPoly's raw low-product context for the transform's product. -/
@[expose] def rawMulLowContextOf (T : PointTransform F Plan) (S : MulSchedule F) :
    CPolynomial.Raw.MulLowContext F where
  mulLow := rawMulLowVia T S
  size_le k p q := by simp [rawMulLowVia]
  coeff_of_lt := coeff_rawMulLowVia T S

end

end LeanVM.Extraction.Fast.FFT
