module

public import LeanVM.Cost.Library
import all Init.Data.List.Sort.Basic

/-!
# Init's hidden definitions, exposed for the compiler

In a `module` file, the bodies of some of Init's definitions are not exposed (well-founded
recursions among them), so the compiler finds no equation to compile them by. Each is copied here
with the same algorithm, so the same cost, exposed, proved equal to Init's on every input, and
registered as a rewrite (`cost_rewrite`): a compiled module that meets Init's definition compiles
the copy.

* `List.merge` (`mergeList`, `merge_eq_mergeList`): the merge of two lists, one comparison per
  element written;
* `List.mergeSort` (`mergeSortList`, `mergeSort_eq_mergeSortList`): Init's merge sort, the list
  halved at `(n + 1)/2` by `take`/`drop` as `MergeSort.Internal.splitInTwo` does by `splitAt`,
  the halves sorted and merged.

Credits: the definitions restate Init's (`Init/Data/List/Sort/Basic.lean`, Lean FRO, Apache-2.0,
"Copyright (c) 2024 Lean FRO", Kim Morrison).
-/

namespace LeanVM.Cost.InitLib

open LeanVM.Cost

@[expose] public section

/-- **`List.merge`, exposed.** -/
def mergeList {α : Type} : List α → List α → (α → α → Bool) → List α
  | [], ys, _ => ys
  | x :: xs, [], _ => x :: xs
  | x :: xs, y :: ys, le =>
    if le x y then x :: mergeList xs (y :: ys) le else y :: mergeList (x :: xs) ys le
termination_by xs ys => xs.length + ys.length

theorem merge_eq_mergeList {α : Type} (xs ys : List α) (le : α → α → Bool) :
    List.merge xs ys le = mergeList xs ys le := by
  induction xs, ys, le using mergeList.induct with
  | case1 ys le => rw [List.nil_merge, mergeList]
  | case2 x xs le => rw [List.merge_right, mergeList]
  | case3 x xs y ys le h ih =>
    rw [List.cons_merge_cons, mergeList]
    simp only [h, ↓reduceIte, ih]
  | case4 x xs y ys le h ih =>
    have h' : le x y = false := by simpa using h
    rw [List.cons_merge_cons, mergeList, h']
    simp only [Bool.false_eq_true, ↓reduceIte, ih]

/-- **`List.mergeSort`, exposed**: halve at `(n + 1)/2`, sort the halves, merge. -/
def mergeSortList {α : Type} : List α → (α → α → Bool) → List α
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: xs, le =>
    let n := (xs.length + 2 + 1) / 2
    mergeList (mergeSortList ((a :: b :: xs).take n) le) (mergeSortList ((a :: b :: xs).drop n) le)
      le
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

theorem mergeSort_eq_mergeSortList {α : Type} (l : List α) (le : α → α → Bool) :
    List.mergeSort l le = mergeSortList l le := by
  induction l, le using mergeSortList.induct with
  | case1 le => rw [List.mergeSort_nil, mergeSortList]
  | case2 a le => rw [List.mergeSort_singleton, mergeSortList]
  | case3 a b xs le n ih1 ih2 =>
    rw [List.mergeSort, mergeSortList]
    simp only [List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      List.length_cons]
    rw [merge_eq_mergeList, ih1, ih2]

end

cost_rewrite merge_eq_mergeList

cost_rewrite mergeSort_eq_mergeSortList

cost_measure mergeList := fun _ xs ys _ ↦ xs.length + ys.length

cost_measure mergeSortList := fun _ xs _ ↦ xs.length

end LeanVM.Cost.InitLib
