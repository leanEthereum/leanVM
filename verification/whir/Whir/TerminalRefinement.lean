import Whir.ArrayAlgebra

/-! Terminal refinement of the executable append-halves equality table and
adjacent-pair folds. All size premises refer to the actual arrays.

The concrete kernels use `1 + r` and `a + r * (a + b)`, so their agreement
already holds over any commutative ring, in particular characteristic two.
The index formulas identify the first coordinate with the least significant
bit; no reversed-point convention or abstract replacement evaluator is used.
These theorems do not supply ring laws for the machine representation `E`. -/
namespace Whir.TerminalRefinement
open Concrete ArrayLayout ArrayAlgebra
open scoped BigOperators

variable {R : Type*} [CommRing R]

private def tableStep (a : Array R) (r : R) : Array R :=
  (a.map fun x => x * (1 + r)) ++ (a.map fun x => x * r)

private theorem eqTable_foldl (point : Array R) :
    eqTable point = point.toList.foldl tableStep #[1] := by
  unfold eqTable
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  exact (Array.foldl_toList ..).symm

@[simp] theorem eqTable_empty : eqTable (#[] : Array R) = #[1] := by
  rw [eqTable_foldl]
  rfl

private theorem tableLoop_size (point : List R) (a : Array R) :
    (point.foldl tableStep a).size = a.size * 2 ^ point.length := by
  induction point generalizing a with
  | nil => simp
  | cons r point ih =>
    simp only [List.foldl_cons, ih, tableStep, Array.size_append, Array.size_map,
      List.length_cons, pow_succ]
    ring

@[simp] theorem size_eqTable (point : Array R) :
    (eqTable point).size = 2 ^ point.size := by
  rw [eqTable_foldl, tableLoop_size]
  simp

private def interleave (c d : R) (a : Array R) : Array R :=
  (a.toList.flatMap fun x => [x * c, x * d]).toArray

private theorem interleave_step (a : Array R) (c d r : R) :
    tableStep (interleave c d a) r = interleave c d (tableStep a r) := by
  apply Array.toList_inj.mp
  simp [tableStep, interleave, List.flatMap_append, List.map_flatMap,
    List.flatMap_map, mul_assoc, mul_comm, mul_left_comm]

private theorem interleave_loop (point : List R) (a : Array R) (c d : R) :
    point.foldl tableStep (interleave c d a) =
      interleave c d (point.foldl tableStep a) := by
  induction point generalizing a with
  | nil => rfl
  | cons r point ih =>
    simp only [List.foldl_cons, interleave_step, ih]

/-- The first array coordinate occupies the least significant index bit,
although the implementation appends halves for each successive coordinate. -/
theorem eqTable_cons_toList (r : R) (point : Array R) :
    (eqTable (#[r] ++ point)).toList =
      (eqTable point).toList.flatMap (fun x => [x * (1 + r), x * r]) := by
  rw [eqTable_foldl]
  rw [Array.toList_append]
  change (point.toList.foldl tableStep (tableStep #[1] r)).toList = _
  have h : tableStep #[1] r = interleave (1 + r) r #[1] := by
    simp [tableStep, interleave]
  rw [h, interleave_loop]
  simp only [interleave, List.toList_toArray, ← eqTable_foldl]

variable [Inhabited R]

private theorem flatMap_pair_get (xs : List R) (c d : R) (i : Nat)
    (hi : i < xs.length) :
    (xs.flatMap (fun x => [x * c, x * d]))[2*i]! = xs[i]! * c ∧
    (xs.flatMap (fun x => [x * c, x * d]))[2*i+1]! = xs[i]! * d := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa [Nat.mul_succ, Nat.add_assoc, List.getElem!_cons_succ] using
        ih i (by simpa using hi)

theorem eqTable_cons_get (r : R) (point : Array R) (i : Nat)
    (hi : i < 2 ^ point.size) :
    (eqTable (#[r] ++ point))[2*i]! = (eqTable point)[i]! * (1 + r) ∧
    (eqTable (#[r] ++ point))[2*i+1]! = (eqTable point)[i]! * r := by
  have h := flatMap_pair_get (eqTable point).toList (1+r) r i (by simpa using hi)
  rw [← eqTable_cons_toList] at h
  simpa only [Array.getElem!_toList] using h

/-- Evaluating the first coordinate is exactly the executable adjacent fold.
The valid-size premise excludes truncation and default reads. -/
theorem mle_cons (a point : Array R) (r : R)
    (ha : a.size = 2 ^ (point.size + 1)) :
    Concrete.mle a (#[r] ++ point) = Concrete.mle (foldLow a r) point := by
  have half : a.size / 2 = 2 ^ point.size := by
    rw [ha, pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
  have pairs (g : Nat → R) :
      (∑ j ∈ Finset.range (2 ^ point.size * 2), g j) =
        ∑ i ∈ Finset.range (2 ^ point.size), (g (2*i) + g (2*i+1)) := by
    generalize 2 ^ point.size = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
      simp [Finset.sum_range_succ, Nat.mul_comm]
  simp only [Concrete.mle, dot_eq_sum, size_eqTable, Array.size_append,
    Array.size_singleton, size_foldLow, half]
  rw [show 1 + point.size = point.size + 1 by omega, ha, min_self, min_self,
    pow_succ, pairs]
  apply Finset.sum_congr rfl
  intro i hi
  have h := eqTable_cons_get r point i (Finset.mem_range.mp hi)
  rw [h.1, h.2, foldLow, getElem!_tab _ _ _ (by simpa [half] using Finset.mem_range.mp hi)]
  unfold foldPair
  ring

/-- An empty point evaluates exactly the first scalar on a valid witness. -/
theorem mle_empty (a : Array R) (ha : a.size = 1) :
    Concrete.mle a #[] = a[0]! := by
  simp [Concrete.mle, dot_eq_sum, ha, eqTable_empty]

private theorem foldLow_terminal_list (point : List R) (a : Array R)
    (ha : a.size = 2 ^ point.length) :
    point.foldl foldLow a = #[Concrete.mle a point.toArray] := by
  induction point generalizing a with
  | nil =>
    have ha' : a.size = 1 := by simpa using ha
    change a = #[Concrete.mle a #[]]
    rw [mle_empty a ha']
    apply Array.ext
    · simpa using ha'
    · intro i hi hi'
      have : i = 0 := by simpa only [ha', Nat.lt_one_iff] using hi
      subst i
      simp [getElem!_pos, hi]
  | cons r point ih =>
    rw [List.foldl_cons, ih (foldLow a r) (by
      simp only [size_foldLow, ha, List.length_cons, pow_succ,
        Nat.mul_div_left _ (by decide : 0 < 2)])]
    congr 1
    have h := mle_cons a point.toArray r (by simpa using ha)
    simpa using h.symm

/-- The actual array-order sequence of executable folds terminates in exactly
one scalar, equal to the actual executable multilinear evaluation. -/
theorem foldLow_terminal (a point : Array R) (ha : a.size = 2 ^ point.size) :
    point.foldl foldLow a = #[Concrete.mle a point] := by
  rw [← Array.foldl_toList]
  simpa using foldLow_terminal_list point.toList a (by simpa using ha)

theorem mle_eq_foldLow_terminal (a point : Array R) (ha : a.size = 2 ^ point.size) :
    Concrete.mle a point = (point.foldl foldLow a)[0]! := by
  rw [foldLow_terminal a point ha]
  simp

@[simp] theorem size_foldLow_terminal (a point : Array R)
    (ha : a.size = 2 ^ point.size) :
    (point.foldl foldLow a).size = 1 := by
  rw [foldLow_terminal a point ha]
  rfl

end Whir.TerminalRefinement
