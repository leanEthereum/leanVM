/-
  LeanVM.Protocol.ToCompPoly.Interpolation

  Lagrange interpolation at a vector of nodes, computed through its weights, with the two facts
  a proof system uses: a polynomial of low degree is its interpolant, and other values
  interpolate to a polynomial that agrees with it at few points. Candidate for CompPoly.
-/

module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Interpolation at nodes

For `N` nodes `x` in a field, `lagrangeWeight x z i` is the value at `z` of the `i`-th Lagrange
basis polynomial, `Π_{j ≠ i} (z - x_j) / Π_{j ≠ i} (x_i - x_j)`, and `interpolateAt x v z` the
value at `z` of the polynomial of degree below `N` taking the values `v` at the nodes:
`Σ_i L_i(z) · v_i`. Both compute; they are Mathlib's `Lagrange.basis` and
`Lagrange.interpolate` evaluated at `z` (`lagrangeWeight_eq`, `interpolateAt_eq`).

* `interpolateAt_eval`: at distinct nodes, a polynomial of degree below `N` is recovered from its
  values at the nodes.
* `card_interpolateAt_eq_le`: values other than a polynomial's at the nodes interpolate to a
  polynomial that agrees with it at `N - 1` points at most.

Over an arbitrary field. Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open Polynomial

@[expose] public section

variable {F : Type*} [Field F] {N : ℕ}

/-- The `i`-th Lagrange weight of the nodes `x` at `z`:
`Π_{j ≠ i} (z - x_j) · (Π_{j ≠ i} (x_i - x_j))⁻¹`. -/
def lagrangeWeight (x : Vector F N) (z : F) (i : Fin N) : F :=
  (∏ j ∈ Finset.univ.erase i, (z - x[j])) * (∏ j ∈ Finset.univ.erase i, (x[i] - x[j]))⁻¹

/-- The value at `z` of the polynomial of degree below `N` that takes the values `v` at the
nodes `x`. -/
def interpolateAt (x v : Vector F N) (z : F) : F := ∑ i : Fin N, lagrangeWeight x z i * v[i]

/-- The inverses of the Lagrange denominators, `(Π_{j ≠ i} (x_i - x_j))⁻¹`: what a verifier
computes once for a fixed set of nodes. -/
def lagrangeInv (x : Vector F N) : Vector F N :=
  Vector.ofFn fun i ↦ (∏ j ∈ Finset.univ.erase i, (x[i] - x[j]))⁻¹

/-- The `i`-th Lagrange weight at `z` from precomputed inverse denominators: no inversion. -/
def lagrangeWeightWith (x inv : Vector F N) (z : F) (i : Fin N) : F :=
  (∏ j ∈ Finset.univ.erase i, (z - x[j])) * inv[i]

/-- With the true inverse denominators, the weight is the Lagrange weight. -/
theorem lagrangeWeightWith_lagrangeInv (x : Vector F N) (z : F) (i : Fin N) :
    lagrangeWeightWith x (lagrangeInv x) z i = lagrangeWeight x z i := by
  simp [lagrangeWeightWith, lagrangeInv, lagrangeWeight]

/-- Interpolation from precomputed inverse denominators. -/
def interpolateWith (x inv v : Vector F N) (z : F) : F :=
  ∑ i : Fin N, lagrangeWeightWith x inv z i * v[i]

/-- With the true inverse denominators, it is the interpolated value. -/
theorem interpolateWith_lagrangeInv (x v : Vector F N) (z : F) :
    interpolateWith x (lagrangeInv x) v z = interpolateAt x v z := by
  simp only [interpolateWith, interpolateAt, lagrangeWeightWith_lagrangeInv]


/-- The weight is Mathlib's Lagrange basis polynomial at `z`. -/
theorem lagrangeWeight_eq (x : Vector F N) (z : F) (i : Fin N) :
    lagrangeWeight x z i = (Lagrange.basis Finset.univ (fun j : Fin N ↦ x[j]) i).eval z := by
  simp only [lagrangeWeight, Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C,
    eval_sub, eval_X]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_comm]

/-- The interpolated value is Mathlib's interpolant at `z`. -/
theorem interpolateAt_eq (x v : Vector F N) (z : F) :
    interpolateAt x v z =
      (Lagrange.interpolate Finset.univ (fun j : Fin N ↦ x[j]) (fun j : Fin N ↦ v[j])).eval z := by
  simp only [interpolateAt, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    lagrangeWeight_eq]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- At distinct nodes, a polynomial of degree below their number is its interpolant: its values
at the nodes interpolate to its value everywhere. -/
theorem interpolateAt_eval (x : Vector F N) (hx : Function.Injective fun j : Fin N ↦ x[j])
    (P : F[X]) (hP : P.degree < N) (z : F) :
    interpolateAt x (Vector.ofFn fun j ↦ P.eval x[j]) z = P.eval z := by
  rw [interpolateAt_eq]
  congr 1
  refine (Lagrange.eq_interpolate_of_eval_eq _ (hx.injOn) ?_ fun j _ ↦ ?_).symm
  · simpa using hP
  · simp

/-- **Few agreements.** At distinct nodes, values `v` other than the values of a polynomial `P`
of degree below `N` interpolate to a polynomial that agrees with `P` at `N - 1` points at most:
the difference is a nonzero polynomial of degree below `N`. -/
theorem card_interpolateAt_eq_le [Fintype F] [DecidableEq F] (x : Vector F N)
    (hx : Function.Injective fun j : Fin N ↦ x[j]) (v : Vector F N) (P : F[X])
    (hP : P.degree < N) (hv : v ≠ Vector.ofFn fun j ↦ P.eval x[j]) :
    (Finset.univ.filter fun z ↦ interpolateAt x v z = P.eval z).card ≤ N - 1 := by
  set Q := Lagrange.interpolate Finset.univ (fun j : Fin N ↦ x[j]) (fun j ↦ v[j]) with hQ
  have hQdeg : Q.degree < N := by
    have := Lagrange.degree_interpolate_lt (r := fun j : Fin N ↦ v[j]) (s := Finset.univ)
      (v := fun j : Fin N ↦ x[j]) hx.injOn
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hne : Q - P ≠ 0 := by
    intro h
    apply hv
    ext j hj
    have hnode := Lagrange.eval_interpolate_at_node (fun j : Fin N ↦ v[j]) (s := Finset.univ)
      hx.injOn (Finset.mem_univ ⟨j, hj⟩)
    rw [← hQ, sub_eq_zero.mp h] at hnode
    simp only [Vector.getElem_ofFn]
    exact hnode.symm
  have hdeg : (Q - P).natDegree ≤ N - 1 := by
    have hlt : (Q - P).degree < N := (degree_sub_le Q P).trans_lt (max_lt hQdeg hP)
    have := (natDegree_lt_iff_degree_lt hne).mpr hlt
    omega
  refine (Polynomial.card_le_degree_of_subset_roots (p := Q - P) ?_).trans hdeg
  intro z hz
  rw [Finset.mem_val, Finset.mem_filter] at hz
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot, eval_sub, hQ, ← interpolateAt_eq, hz.2,
    sub_self]

end
end LeanVM.Protocol
