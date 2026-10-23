/-
  LeanVM.Protocol.ToCompPoly.WeightedCube

  Sums over the Boolean cube against a product of per-coordinate weights, split one coordinate
  at a time. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Weighted sums over the cube

A weight per coordinate, `w k = (w_k(0), w_k(1))`, weighs the cube point `x` by
`∏_k w_k(x_k)` (`cubeWeight`), and `weightedCubeSum w g` is `Σ_x (∏_k w_k(x_k)) · g(x)` for a
function `g` of the point. Unit weights give the plain sum over the cube
(`weightedCubeSum_one`); the weights `(1 - r_k, r_k)` give `Σ_x eq(r, x) · g(x)`
(`weightedCubeSum_eq`).

`weightedCubeSum_succ` splits off the highest coordinate: the sum on `k + 1` coordinates is
`w_k(0)` times the sum on the first `k` with the last fixed to `0`, plus `w_k(1)` times the sum
with it fixed to `1`. `weightedCubeSum_zero` is the sum on no coordinate, the value at the empty
point. `weightedCubeSum_finsetSum`: the weighted sum is linear.

Off the cube, the weight of a point is `prodWeight w z = ∏_k ((1 - z_k) · w_k(0) + z_k · w_k(1))`,
multilinear in each coordinate and `cubeWeight` on the cube (`prodWeight_boolVec`), so summing it
times `g` with unit weights is the weighted sum of `g` (`weightedCubeSum_one_prodWeight`). A
coordinate weighted `(0, 1)` keeps only its value `1`: a function of the low `k` coordinates,
summed against weights `(0, 1)` on every coordinate from `k` on, is its weighted sum on the low
`k` (`weightedCubeSum_lowCoords`). Over an arbitrary commutative ring; nothing here transcribes a
source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The weight of a coordinate's value: `w.1` at `0`, `w.2` at `1`. -/
def bitWeight (w : R × R) (b : Bool) : R := if b then w.2 else w.1

/-- The weight of the cube point with index `x`: the product of its coordinates' weights. -/
def cubeWeight {k : ℕ} (w : Fin k → R × R) (x : Fin (2 ^ k)) : R :=
  ∏ a : Fin k, bitWeight (w a) (x.val.testBit a)

/-- The weighted sum of `g` over the cube: `Σ_x (∏_k w_k(x_k)) · g(x)`. -/
def weightedCubeSum {k : ℕ} (w : Fin k → R × R) (g : Vector R k → R) : R :=
  ∑ x : Fin (2 ^ k), cubeWeight w x * g (boolVec x)

/-- On no coordinate, the weighted sum is the value at the empty point. -/
theorem weightedCubeSum_zero (w : Fin 0 → R × R) (g : Vector R 0 → R) :
    weightedCubeSum w g = g #v[] := by
  have : Unique (Fin (2 ^ 0)) := ⟨⟨0, by decide⟩, fun x ↦ Fin.ext (by have := x.isLt; omega)⟩
  rw [weightedCubeSum, Fintype.sum_unique, cubeWeight, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul]
  congr 1
  exact Vector.ext fun i hi ↦ absurd hi (Nat.not_lt_zero i)

/-- A point on `k` coordinates followed by one more coordinate. -/
private theorem boolVec_cubeIndex_push {k : ℕ} (i : Fin (2 ^ k)) (b : Fin (2 ^ 1)) :
    (boolVec (cubeIndex i b) : Vector R (k + 1)) =
      (boolVec i : Vector R k).push (if b.val.testBit 0 then 1 else 0) := by
  rw [← boolVec_append]
  apply Vector.ext
  intro a ha
  rw [Vector.getElem_append, Vector.getElem_push]
  by_cases h : a < k
  · simp only [h, dite_true]
  · simp only [h, dite_false, boolVec, Vector.getElem_ofFn]
    have hak : a - k = 0 := by omega
    simp only [hak]

/-- Splitting off the highest coordinate: the weighted sum on `k + 1` coordinates is the
weighted sums with the last coordinate fixed to `0` and to `1`, weighted by that coordinate's
weights. -/
theorem weightedCubeSum_succ {k : ℕ} (w : Fin (k + 1) → R × R) (g : Vector R (k + 1) → R) :
    weightedCubeSum w g =
      (w (Fin.last k)).1 * weightedCubeSum (fun a ↦ w a.castSucc) (fun v ↦ g (v.push 0)) +
        (w (Fin.last k)).2 * weightedCubeSum (fun a ↦ w a.castSucc) (fun v ↦ g (v.push 1)) := by
  rw [weightedCubeSum, sum_cube_split (k := k) (m := 1)]
  -- The index type is `Fin (2 ^ 1)`, which is `Fin 2` only after unfolding.
  erw [Fin.sum_univ_two]
  rw [weightedCubeSum, weightedCubeSum, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_ <;>
    rw [boolVec_cubeIndex_push, cubeWeight, Fin.prod_univ_castSucc, cubeWeight] <;>
    simp only [testBit_cubeIndex, Fin.val_last, Fin.val_castSucc, Fin.is_lt, ite_true,
      lt_irrefl, ite_false, Nat.sub_self, bitWeight] <;>
    simp <;> ring

/-- The weighted sum on `k` coordinates, read on `k'` coordinates when `k = k'`. -/
theorem weightedCubeSum_cast {k k' : ℕ} (h : k = k') (w : Fin k → R × R) (g : Vector R k → R) :
    weightedCubeSum w g =
      weightedCubeSum (fun a : Fin k' ↦ w (Fin.cast h.symm a))
        fun v ↦ g (Vector.cast h.symm v) := by
  subst h
  rfl

/-- With unit weights, the weighted sum is the plain sum over the cube. -/
theorem weightedCubeSum_one {k : ℕ} (g : Vector R k → R) :
    weightedCubeSum (fun _ ↦ ((1 : R), (1 : R))) g = ∑ x : Fin (2 ^ k), g (boolVec x) := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [cubeWeight, Finset.prod_eq_one fun a _ ↦ by unfold bitWeight; split <;> rfl, one_mul]

/-- With the weights `(1 - r_k, r_k)`, the weighted sum is `Σ_x eq(r, x) · g(x)`, the weight of
`x` being the Lagrange basis at `r`. -/
theorem weightedCubeSum_eq {k : ℕ} (r : Vector R k) (g : Vector R k → R) :
    weightedCubeSum (fun a ↦ (1 - r[a], r[a])) g =
      ∑ x : Fin (2 ^ k), (lagrangeBasis r)[x] * g (boolVec x) := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [cubeWeight, Fin.getElem_fin, lagrangeBasis_getElem_nat _ x.isLt]
  rfl

/-- The weighted sum is linear: the weighted sum of a finite sum of functions is the sum of
their weighted sums. -/
theorem weightedCubeSum_finsetSum {k : ℕ} {ι : Type*} (s : Finset ι) (w : Fin k → R × R)
    (g : ι → Vector R k → R) :
    weightedCubeSum w (fun z ↦ ∑ i ∈ s, g i z) = ∑ i ∈ s, weightedCubeSum w (g i) := by
  simp only [weightedCubeSum, Finset.mul_sum]
  exact Finset.sum_comm

/-! ## The weight off the cube, and coordinates weighted `(0, 1)` -/

/-- The weight at any point, multilinear in each coordinate: the product over the coordinates of
the line through the two weights, `(1 - z_k) · w_k(0) + z_k · w_k(1)`. At a cube point it is
`cubeWeight` (`prodWeight_boolVec`). -/
def prodWeight {k : ℕ} (w : Fin k → R × R) (z : Vector R k) : R :=
  ∏ a : Fin k, ((1 - z[a]) * (w a).1 + z[a] * (w a).2)

/-- At a cube point, the weight is the cube point's weight. -/
theorem prodWeight_boolVec {k : ℕ} (w : Fin k → R × R) (x : Fin (2 ^ k)) :
    prodWeight w (boolVec x) = cubeWeight w x := by
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  simp only [boolVec, Fin.getElem_fin, Vector.getElem_ofFn, bitWeight]
  split <;> simp

/-- Summing the weight times `g` with unit weights is the weighted sum of `g`. -/
theorem weightedCubeSum_one_prodWeight {k : ℕ} (w : Fin k → R × R) (g : Vector R k → R) :
    weightedCubeSum (fun _ ↦ ((1 : R), (1 : R))) (fun z ↦ prodWeight w z * g z) =
      weightedCubeSum w g := by
  rw [weightedCubeSum_one]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [prodWeight_boolVec]

/-- Coordinates weighted `(0, 1)` keep only their value `1`: a function of the low `k` coordinates,
summed against weights that are `(0, 1)` on every coordinate from `k` on, is its weighted sum on
the low `k` coordinates. -/
theorem weightedCubeSum_lowCoords {k n : ℕ} (h : k ≤ n) (w : Fin n → R × R)
    (hw : ∀ b : Fin n, k ≤ b.val → w b = (0, 1)) (g : Vector R k → R) :
    weightedCubeSum w (fun z ↦ g (lowCoords h z)) =
      weightedCubeSum (fun a : Fin k ↦ w (Fin.castLE h a)) g := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero =>
    congr 1
    funext z
    congr 1
    apply Vector.ext
    intro a ha
    rw [getElem_lowCoords _ _ ha]
  | succ m ih =>
    rw [weightedCubeSum_succ (k := k + m), hw (Fin.last (k + m)) (by simp), zero_mul, zero_add,
      one_mul]
    have hlow : ∀ v : Vector R (k + m), lowCoords h (v.push 1) =
        lowCoords (Nat.le_add_right k m) v := fun v ↦ by
      apply Vector.ext
      intro a ha
      rw [getElem_lowCoords _ _ ha, getElem_lowCoords _ _ ha, Vector.getElem_push_lt]
    simp only [hlow]
    exact ih (Nat.le_add_right k m) _ (fun b hb ↦ hw _ hb)

end
end LeanVM.Protocol
