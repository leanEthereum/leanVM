module

public import NativeVm.Equiv.InsertionSort

/-!
# `stack_offsets`: the model's is the statement's

The model sorts the blocks by insertion (`Model.insertionSort`), the statement by merge sort, by
the same order (largest first, ties by index), strict in the one and not in the other. Both are
sorted permutations of the indices for a total order, so they are one list
(`insertionSort_range_eq_mergeSort`), and the offsets laid along it are the statement's
(`stackOffsets_toSpec`).
-/

public section

namespace NativeVm.Model

open NativeVm.Equiv LeanVM.Protocol.Verifier

/-- The insertion sort of the indices by size, largest first, ties by index, is the statement's
merge sort. -/
theorem insertionSort_range_eq_mergeSort (size : ℕ → ℕ) (n : ℕ) :
    (insertionSort
      (fun i j ↦ decide (size j < size i) || (decide (size i = size j) && decide (i < j)))
      (Array.range n)).toList =
      (List.range n).mergeSort fun i j ↦
        decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j)) := by
  refine List.Perm.eq_of_pairwise
    (le := fun a b ↦
      (decide (size b < size a) || (decide (size a = size b) && decide (a ≤ b))) = true)
    ?_ ?_ ?_ ?_
  · intro a b _ _ h1 h2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2; omega
  · refine (pairwise_insertionSort ?_ ?_ _).imp fun h ↦ ?_
    · intro a b h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    · intro a b c h1 h2
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1 h2 ⊢
      omega
    · simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · exact List.pairwise_mergeSort
      (fun a b c h1 h2 ↦ by
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega) _
  · refine (insertionSort_perm _ _).trans ?_
    simpa using (List.mergeSort_perm _ _).symm

theorem stackOffsets_toSpec (sizes : Array ℕ) :
    (stackOffsets sizes).1.toList = (LeanVM.Protocol.Verifier.stackOffsets sizes.toList).1 ∧
      (stackOffsets sizes).2 = (LeanVM.Protocol.Verifier.stackOffsets sizes.toList).2 := by
  have hg : ∀ i, sizes.getD i 0 = sizes.toList.getD i 0 := fun i ↦ by
    simp [List.getD_eq_getElem?_getD]
  have hfold : ∀ (size : ℕ → ℕ) (l : List ℕ) (acc : Array ℕ × ℕ),
      Prod.map Array.toList id
          (l.foldl (fun acc i ↦ (acc.1.set! i acc.2, acc.2 + 2 ^ size i)) acc) =
        l.foldl (fun acc i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i))
          (Prod.map Array.toList id acc) :=
    fun _ _ _ ↦ (List.foldl_hom (Prod.map Array.toList id) fun x y ↦ by simp).symm
  unfold stackOffsets LeanVM.Protocol.Verifier.stackOffsets
  simp only [hg, Array.length_toList]
  rw [← Array.foldl_toList, insertionSort_range_eq_mergeSort]
  exact ⟨congrArg Prod.fst (hfold _ _ (Array.replicate sizes.size 0, 0)),
    congrArg (log2Ceil ∘ Prod.snd) (hfold _ _ (Array.replicate sizes.size 0, 0))⟩

end NativeVm.Model
