/-
  LeanVM.Protocol.ToCompPoly.IndividualDegree

  Functions of a point that are polynomials of bounded degree in each coordinate separately, and
  the operations that keep the bounds. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
public import LeanVM.Protocol.ToCompPoly.WeightedCube
public import CompPoly.Multivariate.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import CompPoly.Multivariate.MvPolyEquiv.Eval

/-!
# Degree in each coordinate

`DegreeLEAt f k e`: fixing every coordinate of the point but coordinate `k`, `f` is a polynomial
of degree at most `e` in coordinate `k`. `IndividualDegreeLE f d`: that, at the bound `d`, for every
coordinate. It is what a sumcheck needs of its summand: the round polynomial, a sum of such
restrictions, then has degree at most `d`.

The bound in one coordinate is computed by the usual rules: constants have degree `0` (`const`), a
coordinate has degree `1` in itself (`coord_self`) and `0` in the others (`coord_ne`), so does any
function that ignores the coordinate (`of_set_eq`), the extension of a table has degree `1`
(`evalMle`), the bound adds under products (`mul`, `pow`, `prod`) and takes the larger of two
under sums and differences (`add`, `sub`, `sum`), and a polynomial of total degree `d` applied to
functions of degree at most `1` has degree at most `d` (`mvPolynomial_eval`), also with its
coefficients mapped into the ring (`mvPolynomial_eval₂`, and `cmvPolynomial_eval₂` for CompPoly's
polynomials). A product of factors in different coordinates, such as an equality polynomial in
some coordinates times a product of others, is bounded coordinate by coordinate; the weight of a
point off the cube, one affine factor per coordinate, has degree `1` in each (`prodWeight`). Over
an arbitrary commutative ring; nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval Polynomial

@[expose] public section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Fixing every coordinate but coordinate `k`, `f` is a polynomial of degree at most `e` in
coordinate `k`. -/
def DegreeLEAt (f : Vector R n → R) (k e : ℕ) : Prop :=
  ∀ (z : Vector R n) (hk : k < n), ∃ p : R[X], p.natDegree ≤ e ∧ ∀ x, f (z.set k x hk) = p.eval x

/-- `f` has degree at most `d` in every coordinate. -/
def IndividualDegreeLE (f : Vector R n → R) (d : ℕ) : Prop := ∀ k, DegreeLEAt f k d

namespace DegreeLEAt

variable {f g : Vector R n → R} {k d e : ℕ}

/-- A bound is a bound for any larger degree. -/
theorem mono (hf : DegreeLEAt f k d) (h : d ≤ e) : DegreeLEAt f k e := fun z hk ↦
  let ⟨p, hp, hev⟩ := hf z hk
  ⟨p, hp.trans h, hev⟩

/-- A constant has degree `0`. -/
theorem const (c : R) : DegreeLEAt (fun _ : Vector R n ↦ c) k 0 := fun _ _ ↦
  ⟨C c, by simp, fun _ ↦ by simp⟩

/-- A function that ignores coordinate `k` has degree `0` in it. -/
theorem of_set_eq (h : ∀ (z : Vector R n) (hk : k < n) (x : R), f (z.set k x hk) = f z) :
    DegreeLEAt f k 0 := fun z hk ↦
  ⟨C (f z), by simp, fun x ↦ by rw [h z hk x, eval_C]⟩

/-- Coordinate `k` has degree `1` in itself. -/
theorem coord_self (hk : k < n) : DegreeLEAt (fun z : Vector R n ↦ z[k]) k 1 := fun _ _ ↦
  ⟨X, natDegree_X_le, fun x ↦ by simp⟩

/-- Another coordinate has degree `0` in coordinate `k`. -/
theorem coord_ne {i : ℕ} (hi : i < n) (hik : i ≠ k) :
    DegreeLEAt (fun z : Vector R n ↦ z[i]) k 0 :=
  of_set_eq fun _ hk _ ↦ Vector.getElem_set_ne hk hi hik.symm

/-- The bound of a sum is the larger bound. -/
theorem add (hf : DegreeLEAt f k d) (hg : DegreeLEAt g k d) :
    DegreeLEAt (fun z ↦ f z + g z) k d := fun z hk ↦
  let ⟨p, hp, hpe⟩ := hf z hk
  let ⟨q, hq, hqe⟩ := hg z hk
  ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq), fun x ↦ by simp [hpe, hqe]⟩

/-- The bound of a difference is the larger bound. -/
theorem sub (hf : DegreeLEAt f k d) (hg : DegreeLEAt g k d) :
    DegreeLEAt (fun z ↦ f z - g z) k d := fun z hk ↦
  let ⟨p, hp, hpe⟩ := hf z hk
  let ⟨q, hq, hqe⟩ := hg z hk
  ⟨p - q, (natDegree_sub_le _ _).trans (max_le hp hq), fun x ↦ by simp [hpe, hqe]⟩

/-- The bounds of a product add. -/
theorem mul (hf : DegreeLEAt f k d) (hg : DegreeLEAt g k e) :
    DegreeLEAt (fun z ↦ f z * g z) k (d + e) := fun z hk ↦
  let ⟨p, hp, hpe⟩ := hf z hk
  let ⟨q, hq, hqe⟩ := hg z hk
  ⟨p * q, natDegree_mul_le.trans (add_le_add hp hq), fun x ↦ by simp [hpe, hqe]⟩

/-- The bound of a finite sum is a common bound of its terms. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → Vector R n → R}
    (hf : ∀ i ∈ s, DegreeLEAt (f i) k d) : DegreeLEAt (fun z ↦ ∑ i ∈ s, f i z) k d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ((const (0 : R)).mono (Nat.zero_le d) :
      DegreeLEAt (fun _ : Vector R n ↦ (0 : R)) k d)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The bound of a finite product is the sum of its factors' bounds. -/
theorem prod {ι : Type*} (s : Finset ι) {f : ι → Vector R n → R} {d : ι → ℕ}
    (hf : ∀ i ∈ s, DegreeLEAt (f i) k (d i)) :
    DegreeLEAt (fun z ↦ ∏ i ∈ s, f i z) k (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (1 : R) : DegreeLEAt (fun _ : Vector R n ↦ (1 : R)) k 0)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The bound of a power is the exponent times the bound. -/
theorem pow (hf : DegreeLEAt f k d) (m : ℕ) : DegreeLEAt (fun z ↦ f z ^ m) k (m * d) := by
  simpa using prod (Finset.univ : Finset (Fin m)) (f := fun _ ↦ f) (d := fun _ ↦ d)
    fun _ _ ↦ hf

/-- The extension of a table has degree `1` in each coordinate. -/
theorem evalMle (t : CMlPolynomialEval R n) :
    DegreeLEAt (fun z ↦ CMlPolynomialEval.evalMle t z) k 1 := fun z hk ↦
  ⟨C (CMlPolynomialEval.evalMle t (z.set k 0 hk)) +
      X * C (CMlPolynomialEval.evalMle t (z.set k 1 hk) -
        CMlPolynomialEval.evalMle t (z.set k 0 hk)),
    (natDegree_add_le _ _).trans (max_le (by simp)
      (natDegree_mul_le.trans (by simpa using natDegree_X_le))),
    fun x ↦ by
      show CMlPolynomialEval.evalMle t (z.set k x hk) = _
      rw [evalMle_set t z hk x]
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      ring⟩

/-- A polynomial of total degree at most `d`, applied to functions of degree at most `1` in
coordinate `k`, has degree at most `d` in coordinate `k`. -/
theorem mvPolynomial_eval {σ : Type*} (p : MvPolynomial σ R) (hp : p.totalDegree ≤ d)
    {f : σ → Vector R n → R} (hf : ∀ i, DegreeLEAt (f i) k 1) :
    DegreeLEAt (fun z ↦ MvPolynomial.eval (fun i ↦ f i z) p) k d := by
  classical
  have key : ∀ m ∈ p.support, DegreeLEAt
      (fun z ↦ p.coeff m * ∏ i ∈ m.support, f i z ^ m i) k d := by
    intro m hm
    have hdeg : ∑ i ∈ m.support, m i * 1 ≤ d := by
      simpa [Finsupp.sum] using (MvPolynomial.le_totalDegree hm).trans hp
    exact ((const _).mul (prod m.support fun i _ ↦ (hf i).pow (m i))).mono (by simpa using hdeg)
  simpa [MvPolynomial.eval_eq] using sum p.support key

/-- A polynomial of total degree at most `d` over a ring mapped into `R`, applied to functions of
degree at most `1` in coordinate `k`, has degree at most `d` in coordinate `k`. -/
theorem mvPolynomial_eval₂ {S σ : Type*} [CommRing S] (φ : S →+* R) (p : MvPolynomial σ S)
    (hp : p.totalDegree ≤ d) {f : σ → Vector R n → R} (hf : ∀ i, DegreeLEAt (f i) k 1) :
    DegreeLEAt (fun z ↦ MvPolynomial.eval₂ φ (fun i ↦ f i z) p) k d := by
  have hmap : (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset φ p)
  intro z hk
  obtain ⟨q, hq, hqe⟩ := mvPolynomial_eval (MvPolynomial.map φ p) (hmap.trans hp) hf z hk
  exact ⟨q, hq, fun x ↦ by
    show MvPolynomial.eval₂ φ _ p = _
    rw [MvPolynomial.eval₂_eq_eval_map, ← hqe]⟩

/-- The same for CompPoly's computable polynomials. -/
theorem cmvPolynomial_eval₂ {S : Type*} [CommRing S] {m : ℕ} (φ : S →+* R)
    (p : CPoly.CMvPolynomial m S) (hp : p.totalDegree ≤ d) {f : Fin m → Vector R n → R}
    (hf : ∀ i, DegreeLEAt (f i) k 1) :
    DegreeLEAt (fun z ↦ p.eval₂ φ (fun i ↦ f i z)) k d := by
  simp only [CPoly.eval₂_equiv]
  exact mvPolynomial_eval₂ φ _ (by rwa [CPoly.totalDegree_equiv (S := S)] at hp) hf

/-- The weight off the cube, a product of factors each affine in its own coordinate, has degree
at most `1` in each coordinate. -/
theorem prodWeight (w : Fin n → R × R) : DegreeLEAt (LeanVM.Protocol.prodWeight w) k 1 := by
  intro z hk
  have hfac : ∀ a : Fin n, DegreeLEAt (fun z : Vector R n ↦ (1 - z[a]) * (w a).1 + z[a] * (w a).2)
      k (if a.val = k then 1 else 0) := fun a ↦ by
    split_ifs with h
    · subst h
      exact ((((const 1).mono (Nat.zero_le 1)).sub (coord_self a.isLt)).mul (const _)).add
        ((coord_self a.isLt).mul (const _)) |>.mono (by simp)
    · exact (((const 1).sub (coord_ne a.isLt h)).mul (const _)).add
        ((coord_ne a.isLt h).mul (const _)) |>.mono (by simp)
  have hsum : ∑ a : Fin n, (if a.val = k then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single ⟨k, hk⟩
      (fun b _ hb ↦ ite_eq_right_iff.mpr fun h ↦ absurd (Fin.ext h) hb)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp
  exact (hsum ▸ prod Finset.univ fun a _ ↦ hfac a) z hk

end DegreeLEAt

end
end LeanVM.Protocol
