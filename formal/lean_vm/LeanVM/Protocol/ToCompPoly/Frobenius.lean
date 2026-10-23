/-
  LeanVM.Protocol.ToCompPoly.Frobenius

  The Frobenius map in characteristic two on hypercube tables: the Lagrange basis at a point,
  raised to a power of two, is the Lagrange basis at the point raised coordinatewise, so a
  Boolean table's extension commutes with the Frobenius. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
public import Mathlib.Algebra.CharP.Lemmas

/-!
# The Frobenius on tables

In a commutative ring of characteristic two, `x ↦ x ^ 2 ^ k` is a ring homomorphism, and it
fixes `0` and `1`. So on a cube point `b` the equality kernel satisfies
`eq(r, b) ^ 2 ^ k = eq(r ^ 2 ^ k, b)`, the point raised coordinatewise (`lagrangeBasis_frob`),
and the extension of a table whose entries are `0` or `1` satisfies
`t̃(r) ^ 2 ^ k = t̃(r ^ 2 ^ k)` (`evalMle_frob_of_bool`). Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- A point raised to the power `2 ^ k` coordinatewise. -/
def frobPoint {n : ℕ} (k : ℕ) (r : Vector R n) : Vector R n := r.map (· ^ 2 ^ k)

@[simp] theorem frobPoint_getElem {n : ℕ} (k : ℕ) (r : Vector R n) (i : ℕ) (hi : i < n) :
    (frobPoint k r)[i] = r[i] ^ 2 ^ k := by
  simp [frobPoint]

/-- Raising to `2 ^ 0 = 1` changes nothing. -/
@[simp] theorem frobPoint_zero {n : ℕ} (r : Vector R n) : frobPoint 0 r = r := by
  apply Vector.ext
  intro i hi
  simp

variable [CharP R 2]

/-- On a cube index, the Lagrange basis at `r`, raised to `2 ^ k`, is the Lagrange basis at the
point raised coordinatewise. -/
theorem lagrangeBasis_frob {n : ℕ} (k : ℕ) (r : Vector R n) (i : Fin (2 ^ n)) :
    (lagrangeBasis r)[i] ^ 2 ^ k = (lagrangeBasis (frobPoint k r))[i] := by
  rw [lagrangeBasis_getElem, lagrangeBasis_getElem, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  split
  · simp
  · rw [sub_pow_char_pow, one_pow]
    simp

/-- The extension of a table of `0`s and `1`s commutes with the Frobenius:
`t̃(r) ^ 2 ^ k = t̃(r ^ 2 ^ k)`. -/
theorem evalMle_frob_of_bool {n : ℕ} (k : ℕ) (t : CMlPolynomialEval R n)
    (ht : ∀ i : Fin (2 ^ n), t[i] = 0 ∨ t[i] = 1) (r : Vector R n) :
    evalMle t r ^ 2 ^ k = evalMle t (frobPoint k r) := by
  rw [evalMle_eq_sum, evalMle_eq_sum, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, lagrangeBasis_frob]
  rcases ht i with h | h <;> simp [h]

end
end LeanVM.Protocol
