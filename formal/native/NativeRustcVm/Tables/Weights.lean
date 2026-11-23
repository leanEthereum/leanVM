module

public import NativeVm.Model.Tables

/-!
# `tableWeights` coordinate by coordinate

`table_weights` walks the point, multiplying each of the six weights by the coordinate's factor
(`twStep`); after `c` coordinates the weights are the model's fold over the point's first `c`
(`twPrefix`, `twPrefix_succ`), after all of them `tableWeights` (`tableWeights_eq`). Weight `j`
after a coordinate (`getElem_twStep`).
-/

namespace NativeRustcVm.Tables

open NativeVm.Model

@[expose] public section

/-- One coordinate `(challenge, coord)` of `tableWeights`. -/
def twStep (heights : Array Nat) (eqp : Array EW) (weights : Array EW) (x : EW × Nat) :
    Array EW :=
  Array.zipWith (fun weight height ↦ weight *
    if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1) weights heights

/-- The weights after the point's first `c` coordinates. -/
def twPrefix (heights : Array Nat) (eqp point : Array EW) (c : Nat) : Array EW :=
  (point.toList.zipIdx.take c).foldl (twStep heights eqp) (heights.map fun _ ↦ 1)

end

public section

theorem tableWeights_eq (heights : Array Nat) (eqp point : Array EW) :
    tableWeights heights eqp point = twPrefix heights eqp point point.size := by
  unfold tableWeights twPrefix
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.take_of_length_le (by simp)]
  rfl

theorem twPrefix_zero (heights : Array Nat) (eqp point : Array EW) :
    twPrefix heights eqp point 0 = heights.map fun _ ↦ 1 := by
  simp [twPrefix]

theorem twPrefix_succ (heights : Array Nat) (eqp point : Array EW) {c : Nat}
    (hc : c < point.size) :
    twPrefix heights eqp point (c + 1) =
      twStep heights eqp (twPrefix heights eqp point c) (point[c], c) := by
  unfold twPrefix
  have hl : c < point.toList.zipIdx.length := by simpa using hc
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, List.foldl_append]
  simp [List.getElem_zipIdx]

theorem size_twStep (heights : Array Nat) (eqp weights : Array EW) (x : EW × Nat)
    (h : weights.size = heights.size) : (twStep heights eqp weights x).size = heights.size := by
  simp [twStep, h]

theorem size_twPrefix (heights : Array Nat) (eqp point : Array EW) (c : Nat) :
    (twPrefix heights eqp point c).size = heights.size := by
  unfold twPrefix
  generalize point.toList.zipIdx.take c = l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih => rw [List.foldl_append]; simp [size_twStep _ _ _ _ ih]

theorem getElem_twStep (heights : Array Nat) (eqp weights : Array EW) (x : EW × Nat) {j : Nat}
    (hj : j < (twStep heights eqp weights x).size) :
    (twStep heights eqp weights x)[j] = weights[j]'(by simp [twStep] at hj; omega) *
      if x.2 < heights[j]'(by simp [twStep] at hj; omega) then 1 + eqp.getD x.2 0 + x.1
      else x.1 := by
  simp [twStep]

end

end NativeRustcVm.Tables
