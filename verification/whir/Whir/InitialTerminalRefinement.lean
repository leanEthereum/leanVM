import Whir.QueryRefinement
import Whir.SuccinctPointWeight

namespace Whir.InitialTerminalRefinement
open Concrete ArrayLayout ArrayAlgebra ExecutableOOD SuccinctPointWeight
open scoped BigOperators
variable {R : Type*} [CommRing R] [CharP R 2] [Inhabited R]

/-- Disintegration in the actual little-endian array layout. -/
theorem mle_append (a : Array R) (low high : Array R)
    (ha : a.size = 2 ^ (low.size + high.size)) :
    Concrete.mle a (low ++ high) =
      Concrete.mle (tab (2 ^ low.size) fun row =>
        Concrete.mle (tab (2 ^ high.size) fun lane => a[lane * 2 ^ low.size + row]!) high) low := by
  let x : Fin low.size → R := fun i => low[i]
  let y : Fin high.size → R := fun i => high[i]
  have hx : Array.ofFn x = low := by ext i hi hj <;> simp [x]
  have hy : Array.ofFn y = high := by ext i hi hj <;> simp [y]
  have hxy : Array.ofFn (Fin.addCases x y) = low ++ high := by
    change Array.ofFn (Fin.append x y) = low ++ high
    apply Array.toList_inj.mp
    simpa only [Array.toList_ofFn, List.ofFn_fin_append, Array.toList_append] using
      congrArg₂ (fun a b : Array R => a.toList ++ b.toList) hx hy
  rw [← hxy, mle_eq_cube a _ ha]
  have hlow := mle_eq_cube
    (tab (2 ^ low.size) fun row =>
      Concrete.mle (tab (2 ^ high.size) fun lane => a[lane * 2 ^ low.size + row]!) high) x (by simp)
  rw [hx] at hlow
  rw [hlow]
  simp only [Whir.mle, innerProduct, decode]
  rw [← Equiv.sum_comp (cubeAppendEquiv low.size high.size)]
  simp only [Fintype.sum_prod_type, cubeAppendEquiv, Equiv.coe_fn_mk,
    eqWeight_append, cubeIndex_append]
  apply Finset.sum_congr rfl
  intro u _
  rw [getElem!_tab _ _ _ (cubeIndex_lt u)]
  have hhigh := mle_eq_cube
    (tab (2 ^ high.size) fun lane => a[lane * 2 ^ low.size + cubeIndex u]!) y (by simp)
  rw [hy] at hhigh
  rw [hhigh]
  simp only [Whir.mle, innerProduct, decode, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [getElem!_tab _ _ _ (cubeIndex_lt v)]
  simp only [Nat.mul_comm, Nat.add_comm]
  ring

/-- L0 folds the top variables first, while every later context remains in
unrotated low-variable order. -/
theorem mle_foldLane_initial (a initial low : Array R)
    (ha : a.size = 2 ^ (low.size + initial.size)) :
    Concrete.mle (initial.foldl (fun b r => foldLane b (2 ^ low.size) r) a) low =
      Concrete.mle a (low ++ initial) := by
  rw [QueryRefinement.foldLane_blocks a initial (2 ^ low.size)
    (by rw [ha, pow_add, Nat.mul_comm])]
  exact (mle_append a low initial ha).symm

omit [CommRing R] [CharP R 2] [Inhabited R] in
theorem rotate_initial (initial low : Array R) :
    rotatePoint initial.size (initial ++ low) = low ++ initial := by
  apply Array.toList_inj.mp
  rw [rotatePoint_terminalPoint _ _ (by simp)]
  simpa using Layout.terminalPoint_order initial.toList low.toList

end Whir.InitialTerminalRefinement
