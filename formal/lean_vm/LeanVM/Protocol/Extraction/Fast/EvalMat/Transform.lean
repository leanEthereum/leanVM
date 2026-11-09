module

public import CompPoly.Univariate.ToPoly

/-!
# Evaluation transforms

An `EvalTransform F` is a family of transforms of sizes `2^j`, `j ≤ maxLog`: `fwd j p` is the
array of `p`'s values at the `2^j` points `point j v`, `v < 2^j`, for `p` of fewer than `2^j`
coefficients, and `inv j` recovers such a `p` from its values. Over `K = GF(2^64)` the additive
NTT is one (`maxLog = 64`, the points `x_v`); over any field, multipoint evaluation and
interpolation at `2^j` distinct points.

Consequences: values multiply pointwise (`fwd_mul_getD`), so a sum of
products of polynomials whose degree stays below `2^j` is the inverse transform of the sum of the
pointwise products of their transforms (`inv_sum_mul`): the evaluation-domain product.
-/

namespace LeanVM.Extraction.Fast.EvalMat

open CompPoly

public section

/-- **A family of evaluation transforms** of sizes `2^j`, `j ≤ maxLog`, over `F`. -/
structure EvalTransform (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- The largest size's logarithm. -/
  maxLog : ℕ
  /-- The evaluation points of size `2^j`: `point j v`, `v < 2^j`. -/
  point : ℕ → ℕ → F
  /-- The forward transform: monomial coefficients to `2^j` values. -/
  fwd : ℕ → CPolynomial F → Array F
  /-- The inverse transform: `2^j` values to monomial coefficients. -/
  inv : ℕ → Array F → CPolynomial F
  /-- The forward transform has `2^j` entries. -/
  size_fwd : ∀ j p, j ≤ maxLog → p.natDegree < 2 ^ j → (fwd j p).size = 2 ^ j
  /-- The forward transform evaluates. -/
  fwd_getD : ∀ j p, j ≤ maxLog → p.natDegree < 2 ^ j →
    ∀ v < 2 ^ j, (fwd j p).getD v 0 = p.eval (point j v)
  /-- The inverse transform inverts the forward one below `2^j` coefficients. -/
  inv_fwd : ∀ j p, j ≤ maxLog → p.natDegree < 2 ^ j → inv j (fwd j p) = p

namespace EvalTransform

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] (T : EvalTransform F)

theorem natDegree_mul_le' (p q : CPolynomial F) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
    CPolynomial.toPoly_mul]
  exact Polynomial.natDegree_mul_le

theorem natDegree_sum_le (s : ℕ) (f : ℕ → CPolynomial F) (d : ℕ)
    (hf : ∀ k < s, (f k).natDegree ≤ d) :
    (∑ k ∈ Finset.range s, f k).natDegree ≤ d := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  rw [← CPolynomial.natDegree_toPoly]
  exact hf k (Finset.mem_range.mp hk)

theorem eval_sum (x : F) (s : ℕ) (f : ℕ → CPolynomial F) :
    (∑ k ∈ Finset.range s, f k).eval x = ∑ k ∈ Finset.range s, (f k).eval x := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_sum, Polynomial.eval_finsetSum]
  simp only [CPolynomial.eval_toPoly]

/-- **Values multiply pointwise** while the product has fewer than `2^j` coefficients. -/
theorem fwd_mul_getD {j : ℕ} (hj : j ≤ T.maxLog) {p q : CPolynomial F}
    (hpq : p.natDegree + q.natDegree < 2 ^ j) {v : ℕ} (hv : v < 2 ^ j) :
    (T.fwd j (p * q)).getD v 0 = (T.fwd j p).getD v 0 * (T.fwd j q).getD v 0 := by
  have hm : (p * q).natDegree < 2 ^ j := lt_of_le_of_lt (natDegree_mul_le' p q) hpq
  rw [T.fwd_getD j _ hj hm v hv, T.fwd_getD j _ hj (by omega) v hv,
    T.fwd_getD j _ hj (by omega) v hv, CPolynomial.eval_mul]

/-- **Values multiply pointwise**, as arrays. -/
theorem fwd_mul {j : ℕ} (hj : j ≤ T.maxLog) {p q : CPolynomial F}
    (hpq : p.natDegree + q.natDegree < 2 ^ j) :
    T.fwd j (p * q) =
      Array.ofFn fun v : Fin (2 ^ j) ↦ (T.fwd j p).getD v 0 * (T.fwd j q).getD v 0 := by
  have hm : (p * q).natDegree < 2 ^ j := lt_of_le_of_lt (natDegree_mul_le' p q) hpq
  apply Array.ext (by rw [T.size_fwd j _ hj hm, Array.size_ofFn])
  intro v h₁ h₂
  rw [T.size_fwd j _ hj hm] at h₁
  have := T.fwd_mul_getD hj hpq h₁
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rwa [T.size_fwd j _ hj hm]),
    Option.getD_some] at this
  rw [this, Array.getElem_ofFn]

/-- The left fold of a sum over `List.range s`. -/
theorem foldl_range_add {M : Type*} [AddCommMonoid M] (g : ℕ → M) (s : ℕ) :
    (List.range s).foldl (fun acc k ↦ acc + g k) 0 = ∑ k ∈ Finset.range s, g k := by
  induction s with
  | zero => rfl
  | succ s ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

/-- **The evaluation-domain sum of products**: the inverse transform of
`v ↦ Σ_{k<s} fwd(f k)[v] · fwd(g k)[v]` is `Σ_{k<s} f k · g k`, when the degrees of the `f k` are
at most `d₁`, those of the `g k` at most `d₂`, and `d₁ + d₂ < 2^j`. -/
theorem inv_sum_mul {j : ℕ} (hj : j ≤ T.maxLog) (s : ℕ) (f g : ℕ → CPolynomial F) {d₁ d₂ : ℕ}
    (hf : ∀ k < s, (f k).natDegree ≤ d₁) (hg : ∀ k < s, (g k).natDegree ≤ d₂)
    (hd : d₁ + d₂ < 2 ^ j) :
    T.inv j (Array.ofFn fun v : Fin (2 ^ j) ↦
        (List.range s).foldl
          (fun acc k ↦ acc + (T.fwd j (f k)).getD v 0 * (T.fwd j (g k)).getD v 0) 0) =
      ∑ k ∈ Finset.range s, f k * g k := by
  set P := ∑ k ∈ Finset.range s, f k * g k
  have hP : P.natDegree < 2 ^ j :=
    lt_of_le_of_lt (natDegree_sum_le s _ (d₁ + d₂) fun k hk ↦
      (natDegree_mul_le' _ _).trans (Nat.add_le_add (hf k hk) (hg k hk))) hd
  have harr : (Array.ofFn fun v : Fin (2 ^ j) ↦
        (List.range s).foldl
          (fun acc k ↦ acc + (T.fwd j (f k)).getD v 0 * (T.fwd j (g k)).getD v 0) 0) =
      T.fwd j P := by
    apply Array.ext (by rw [T.size_fwd j _ hj hP, Array.size_ofFn])
    intro v h₁ h₂
    rw [Array.size_ofFn] at h₁
    have hv := T.fwd_getD j P hj hP v h₁
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h₂, Option.getD_some] at hv
    rw [Array.getElem_ofFn, hv, eval_sum, foldl_range_add]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk := Finset.mem_range.mp hk
    rw [T.fwd_getD j _ hj (by have := hf k hk; omega) v h₁,
      T.fwd_getD j _ hj (by have := hg k hk; omega) v h₁, CPolynomial.eval_mul]
  rw [harr, T.inv_fwd j P hj hP]

end EvalTransform

end

end LeanVM.Extraction.Fast.EvalMat
