/-
  LeanVM.Guest.Batch.Bytecode

  The batching sumcheck on the split table: the polynomial it sums over the cube, and that sum.
-/

module

public import LeanVM.Guest.Batch.Cube
public import Statement.LeanVmGuestCompleteness

/-!
# The batching's sumcheck

The batching combines the children's claims on the split table with the lambdas `l`, one pair per
child (its fresh claim's, at its point and the column challenges `column`, and its carried
claim's), and runs a sumcheck of `splitPoly t`: the table's multilinear extension times the
weight `batchedBytecodeWeight`, the lambdas' combination of the claims' equality weights. For a
table `t` of `2^n` entries, its cube sum is the lambdas' combination of the table's values at the
claims' points (`split_cubeSum`), and it is quadratic along each coordinate
(`split_quadraticIn`). The table is the split program's, `(splitTable bytecode).map ofK`.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **The polynomial the batching sums**: the table's multilinear extension times the batched
weight. -/
def splitPoly (t : List E) (cs : List ChildClaims) (l : List (E × E)) (column y : List E) : E :=
  multilinearEval t y * batchedBytecodeWeight cs l column y

/-- The lambdas' combination of the table's values at the claims' points: a fresh claim's point
followed by the column challenges, a carried claim's point. -/
def splitTrue (t : List E) (cs : List ChildClaims) (l : List (E × E)) (column : List E) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * multilinearEval t (c.freshClaim.point ++ column) +
      l.2 * multilinearEval t c.carriedClaim.bytecodePoint) cs l)

/-- The claims' points have `n` coordinates: a fresh claim's with the column challenges, a
carried claim's. -/
def PointsOf (n : ℕ) (cs : List ChildClaims) (column : List E) : Prop :=
  ∀ c ∈ cs, (c.freshClaim.point ++ column).length = n ∧ c.carriedClaim.bytecodePoint.length = n

/-- Against the equality weight of a point of `n` coordinates, the cube sum of the extension of
a table of `2^n` entries is its value at the point. -/
theorem sum_cube_mul_eqEval {n : ℕ} {t : List E} (ht : t.length = 2 ^ n) {p : List E}
    (hp : p.length = n) :
    ∑ y ∈ Finset.range (2 ^ n),
        multilinearEval t (Tables.boolPoint n y) * eqEval p (Tables.boolPoint n y) =
      multilinearEval t p := by
  rw [Tables.multilinearEval_eq_sum n t p ht hp]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Tables.multilinearEval_boolPoint_getD n t y ht (Finset.mem_range.mp hy),
    Tables.eqEval_comm]

/-- The batched weight is multilinear. -/
theorem multilinear_weight {n : ℕ} {cs : List ChildClaims} {column : List E}
    (hp : PointsOf n cs column) (l : List (E × E)) :
    Multilinear n (batchedBytecodeWeight cs l column) := by
  unfold batchedBytecodeWeight
  simp only [← List.map_uncurry_zip_eq_zipWith]
  refine multilinear_sumE _ fun a ha ↦ ?_
  obtain ⟨c, l⟩ := a
  have hc := hp c (List.of_mem_zip ha).1
  exact (Multilinear.const_mul _ (multilinear_eqEval hc.1)).add
    (Multilinear.const_mul _ (multilinear_eqEval hc.2))

/-- **The cube sum is the values' combination**, for a table of `2^n` entries and points of `n`
coordinates. -/
theorem split_cubeSum {n : ℕ} {t : List E} (ht : t.length = 2 ^ n) {cs : List ChildClaims}
    {column : List E} (hp : PointsOf n cs column) (l : List (E × E)) :
    cubeSum n (splitPoly t cs l column) [] = splitTrue t cs l column := by
  simp only [cubeSum, List.length_nil, Nat.sub_zero, List.nil_append]
  induction cs generalizing l with
  | nil => simp [splitPoly, batchedBytecodeWeight, splitTrue, sumE]
  | cons c cs ih =>
    cases l with
    | nil => simp [splitPoly, batchedBytecodeWeight, splitTrue, sumE]
    | cons l ls =>
      have ih' := ih (fun c' hc' ↦ hp c' (List.mem_cons_of_mem _ hc')) ls
      have hc := hp c List.mem_cons_self
      simp only [splitPoly, batchedBytecodeWeight, splitTrue, List.zipWith_cons_cons,
        Tables.sumE_eq, List.sum_cons] at ih' ⊢
      rw [← ih', ← sum_cube_mul_eqEval ht hc.1, ← sum_cube_mul_eqEval ht hc.2, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      ring

/-- The batched polynomial is quadratic along each coordinate. -/
theorem split_quadraticIn {n : ℕ} {t : List E} (ht : t.length = 2 ^ n) {cs : List ChildClaims}
    {column : List E} (hp : PointsOf n cs column) (l : List (E × E)) :
    QuadraticIn n (splitPoly t cs l column) :=
  quadraticIn_mul (multilinear_multilinearEval ht) (multilinear_weight hp l)

end
end LeanVM.Guest.Batch
