/-
  LeanVM.Guest.Batch.Bytecode

  The bytecode's batching sumcheck: the polynomial it sums over the cube, and that sum.
-/

module

public import LeanVM.Guest.Batch.Cube
public import Statement.LeanVmGuest
public import LeanVM.Guest.Batch.Def
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier

/-!
# The bytecode's batching

`batch` combines the children's claims on the bytecode with the lambdas `lB`, one pair per child
(its proof's claim, its statement's), and runs a sumcheck of `bytecodePoly`: the bytecode's
multilinear extension times the weight `batchedBytecodeWeight`, the lambdas' combination of the claims'
equality weights. Its cube sum is the lambdas' combination of the bytecode's true values at the
claims' points (`bytecode_cubeSum`), and it is quadratic along each coordinate
(`bytecode_quadraticIn`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **The polynomial the bytecode's batching sums**: the bytecode's multilinear extension times
the batched weight. -/
def bytecodePoly (bytecode : List K) (cs : List ChildClaims) (lB : List (E × E)) (y : List E) : E :=
  multilinearEval (bytecode.map ofK) y * batchedBytecodeWeight cs lB y

/-- The lambdas' combination of the bytecode's true values at the claims' points. -/
def bytecodeTrue (bytecode : List K) (cs : List ChildClaims) (lB : List (E × E)) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * multilinearEval (bytecode.map ofK) c.freshClaim.bytecodePoint +
      l.2 * multilinearEval (bytecode.map ofK) c.carriedClaim.bytecodePoint) cs lB)

/-- Against the equality weight of a point of `n` coordinates, the cube sum of the extension of
a table of `2^n` entries is its value at the point. -/
theorem sum_cube_mul_eqEval {n : ℕ} {t : List E} (ht : t.length = 2 ^ n) {p : List E}
    (hp : p.length = n) :
    ∑ y ∈ Finset.range (2 ^ n),
        multilinearEval t (EndToEnd.boolPoint n y) * eqEval p (EndToEnd.boolPoint n y) =
      multilinearEval t p := by
  rw [Whir.Complete.multilinearEval_eq_sum n t p ht hp]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [EndToEnd.Complete.multilinearEval_boolPoint_getD n t y ht (Finset.mem_range.mp hy),
    Whir.Complete.eqEval_comm]

/-- The bytecode's batched weight is multilinear. -/
theorem multilinear_bytecodeWeight {n : ℕ} {cs : List ChildClaims} (hp : ∀ c ∈ cs,
      c.freshClaim.bytecodePoint.length = n ∧ c.carriedClaim.bytecodePoint.length = n)
    (lB : List (E × E)) : Multilinear n (batchedBytecodeWeight cs lB) := by
  unfold batchedBytecodeWeight
  simp only [← List.map_uncurry_zip_eq_zipWith]
  refine multilinear_sumE _ fun a ha ↦ ?_
  obtain ⟨c, l⟩ := a
  have hc := hp c (List.of_mem_zip ha).1
  exact (Multilinear.const_mul _ (multilinear_eqEval hc.1)).add
    (Multilinear.const_mul _ (multilinear_eqEval hc.2))

/-- **The cube sum is the true values' combination**, for a bytecode of `2^n` words and points
of `n` coordinates. -/
theorem bytecode_cubeSum {n : ℕ} {bytecode : List K} (hb : bytecode.length = 2 ^ n)
    {cs : List ChildClaims} (hp : ∀ c ∈ cs,
      c.freshClaim.bytecodePoint.length = n ∧ c.carriedClaim.bytecodePoint.length = n)
    (lB : List (E × E)) :
    cubeSum n (bytecodePoly bytecode cs lB) [] = bytecodeTrue bytecode cs lB := by
  have hL : (bytecode.map ofK).length = 2 ^ n := by rw [List.length_map, hb]
  simp only [cubeSum, List.length_nil, Nat.sub_zero, List.nil_append]
  induction cs generalizing lB with
  | nil => simp [bytecodePoly, batchedBytecodeWeight, bytecodeTrue, sumE]
  | cons c cs ih =>
    cases lB with
    | nil => simp [bytecodePoly, batchedBytecodeWeight, bytecodeTrue, sumE]
    | cons l lB =>
      have ih' := ih (fun c' hc' ↦ hp c' (List.mem_cons_of_mem _ hc')) lB
      have hc := hp c List.mem_cons_self
      simp only [bytecodePoly, batchedBytecodeWeight, bytecodeTrue, List.zipWith_cons_cons,
        Whir.Complete.sumE_eq, List.sum_cons] at ih' ⊢
      rw [← ih', ← sum_cube_mul_eqEval hL hc.1, ← sum_cube_mul_eqEval hL hc.2, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      ring

/-- The bytecode's batched polynomial is quadratic along each coordinate. -/
theorem bytecode_quadraticIn {n : ℕ} {bytecode : List K} (hb : bytecode.length = 2 ^ n)
    {cs : List ChildClaims} (hp : ∀ c ∈ cs,
      c.freshClaim.bytecodePoint.length = n ∧ c.carriedClaim.bytecodePoint.length = n)
    (lB : List (E × E)) :
    QuadraticIn n (bytecodePoly bytecode cs lB) :=
  quadraticIn_mul (multilinear_multilinearEval (by rw [List.length_map, hb]))
    (multilinear_bytecodeWeight hp lB)

end
end LeanVM.Guest.Batch
