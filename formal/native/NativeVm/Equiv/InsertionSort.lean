module

public import NativeVm.Model.Layout

/-!
# The model's insertion sort sorts

`Model.insertionSort lt` (`NativeVm/Model/Layout.lean`, core's `Array.insertionSort` spelled out)
is, on lists, each element in turn bubbled down the sorted prefix (`bubble`, the prefix held
reversed) while `lt` puts it before its neighbour (`insertionSort_toList`). For an `lt` that is
asymmetric with a transitive negation, the result is a permutation of the input
(`insertionSort_perm`) sorted by `le a b := !lt b a` (`pairwise_insertionSort`).
-/

public section

namespace NativeVm.Equiv

open NativeVm.Model

variable {α : Type} [Inhabited α] (lt : α → α → Bool)
/-- Bubble `x` down a list held reversed (its last element first): past every `p` with
`lt x p`. -/
def bubble (x : α) : List α → List α
  | [] => [x]
  | p :: ps => if lt x p then p :: bubble x ps else x :: p :: ps

theorem swapDown_toList (xs : Array α) (j : ℕ) (h : j < xs.size) :
    (swapDown lt xs j).toList =
      (bubble lt xs[j] (xs.toList.take j).reverse).reverse ++ xs.toList.drop (j + 1) := by
  induction j generalizing xs with
  | zero =>
    have hl : 0 < xs.toList.length := by simpa using h
    simp only [swapDown, List.take_zero, List.reverse_nil, bubble, List.reverse_cons,
      List.nil_append, List.cons_append, Nat.zero_add]
    rw [← Array.getElem_toList hl]
    exact (List.getElem_cons_drop (h := hl)).symm
  | succ j ih =>
    have hj : j < xs.size := by omega
    have hsplit : xs.toList =
        xs.toList.take j ++ xs[j] :: xs[j + 1] :: xs.toList.drop (j + 1 + 1) := by
      conv_lhs => rw [← List.take_append_drop j xs.toList]
      rw [← Array.getElem_toList (i := j + 1) (by simpa using h), List.getElem_cons_drop,
        ← Array.getElem_toList (i := j) (by simpa using hj), List.getElem_cons_drop]
    have hAl : (xs.toList.take j).length = j := by simp; omega
    generalize xs.toList.take j = A at hsplit hAl
    generalize xs.toList.drop (j + 1 + 1) = R at hsplit
    have htake : xs.toList.take (j + 1) = A ++ [xs[j]] := by
      rw [hsplit, List.take_append]; simp [hAl]
    simp only [swapDown, getElem!_pos xs (j + 1) h, getElem!_pos xs j hj, htake,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, bubble]
    split
    · have hys : (xs.swapIfInBounds (j + 1) j).toList = A ++ xs[j + 1] :: xs[j] :: R := by
        simp only [Array.swapIfInBounds_def, h, hj, dite_true, Array.toList_swap]
        rw [hsplit]
        simp [hAl, List.set_append_right]
      have hsz : j < (xs.swapIfInBounds (j + 1) j).size := by simp; omega
      have hy : (xs.swapIfInBounds (j + 1) j)[j] = xs[j + 1] := by
        rw [← Array.getElem_toList (by simpa using hsz)]; simp [hys, hAl]
      rw [ih _ hsz, hy, hys, List.drop_append, List.drop_eq_nil_of_le (by omega), hAl,
        (by omega : j + 1 - j = 1), List.take_left' hAl]
      simp
    · conv_lhs => rw [hsplit]
      simp

omit [Inhabited α] in
theorem bubble_perm (x : α) : ∀ r : List α, (bubble lt x r).Perm (x :: r)
  | [] => .refl _
  | p :: ps => by
    unfold bubble
    split
    · exact ((bubble_perm x ps).cons p).trans (.swap x p ps)
    · exact .refl _

omit [Inhabited α] in
theorem length_bubble (x : α) (r : List α) : (bubble lt x r).length = r.length + 1 :=
  (bubble_perm lt x r).length_eq

/-- The sorted prefix reversed: `bubble` each element in turn. -/
def bubbleAll (l : List α) : List α := l.foldl (fun r x ↦ bubble lt x r) []

omit [Inhabited α] in
theorem length_bubbleAll (l : List α) : (bubbleAll lt l).length = l.length := by
  unfold bubbleAll
  suffices ∀ r, (l.foldl (fun r x ↦ bubble lt x r) r).length = r.length + l.length by
    simpa using this []
  induction l with
  | nil => simp
  | cons x l ih => intro r; simp [ih, length_bubble]; omega

theorem insertionSort_toList (xs : Array α) :
    (insertionSort lt xs).toList = (bubbleAll lt xs.toList).reverse := by
  have hl : xs.toList.length = xs.size := Array.length_toList
  have key : ∀ i ≤ xs.size, ((List.range i).foldl (fun acc i ↦ swapDown lt acc i) xs).toList =
      (bubbleAll lt (xs.toList.take i)).reverse ++ xs.toList.drop i := by
    intro i
    induction i with
    | zero => intro _; simp [bubbleAll]
    | succ i ih =>
      intro hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hys' : (List.range i).foldl (fun acc i ↦ swapDown lt acc i) xs = ys
      have hys := ih (by omega)
      rw [hys'] at hys
      have hlen : (bubbleAll lt (xs.toList.take i)).length = i := by
        rw [length_bubbleAll]; simp; omega
      have hysz : i < ys.size := by
        rw [← Array.length_toList, hys]; simp [hlen]; omega
      have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [← Array.getElem_toList (i := i) (by omega), List.getElem_cons_drop]
      have hyi : ys[i] = xs[i] := by
        rw [← Array.getElem_toList (by simpa using hysz)]
        simp only [hys, hdrop]
        rw [List.getElem_append_right (by simp [hlen])]; simp [hlen]
      rw [swapDown_toList lt ys i hysz, hyi]
      have htake : ys.toList.take i = (bubbleAll lt (xs.toList.take i)).reverse := by
        rw [hys]; exact List.take_left' (by simp [hlen])
      have hdrop' : ys.toList.drop (i + 1) = xs.toList.drop (i + 1) := by
        rw [hys, hdrop, List.drop_append, List.length_reverse, hlen,
          List.drop_eq_nil_of_le (by simp [hlen]), (by omega : i + 1 - i = 1)]; rfl
      rw [htake, hdrop', List.reverse_reverse, List.take_add_one,
        List.getElem?_eq_getElem (by omega)]
      simp [bubbleAll, List.foldl_append]
  unfold insertionSort
  rw [key xs.size le_rfl, ← hl, List.take_length, List.drop_length, List.append_nil]

theorem insertionSort_perm (xs : Array α) : (insertionSort lt xs).toList.Perm xs.toList := by
  rw [insertionSort_toList]
  refine (List.reverse_perm _).trans ?_
  unfold bubbleAll
  suffices ∀ r, (xs.toList.foldl (fun r x ↦ bubble lt x r) r).Perm (r ++ xs.toList) by
    simpa using this []
  induction xs.toList with
  | nil => intro r; simp
  | cons x l ih =>
    intro r
    simp only [List.foldl_cons]
    refine (ih _).trans ?_
    refine ((bubble_perm lt x r).append_right l).trans ?_
    exact List.perm_middle.symm

variable {lt}

omit [Inhabited α] in
theorem bubble_pairwise (hasymm : ∀ a b, lt a b → lt b a = false)
    (htrans : ∀ a b c, lt b a = false → lt c b = false → lt c a = false) (x : α) :
    ∀ r : List α, r.Pairwise (fun a b ↦ lt a b = false) →
      (bubble lt x r).Pairwise (fun a b ↦ lt a b = false)
  | [], _ => by simp [bubble]
  | p :: ps, h => by
    rw [List.pairwise_cons] at h
    unfold bubble
    split
    · rename_i hxp
      refine List.pairwise_cons.2 ⟨fun y hy ↦ ?_, bubble_pairwise hasymm htrans x ps h.2⟩
      rcases List.mem_cons.1 ((bubble_perm lt x ps).mem_iff.1 hy) with rfl | hy
      · exact hasymm _ _ hxp
      · exact h.1 y hy
    · rename_i hxp
      refine List.pairwise_cons.2 ⟨fun y hy ↦ ?_, List.pairwise_cons.2 h⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · simpa using hxp
      · exact htrans _ _ _ (h.1 y hy) (by simpa using hxp)

/-- The sort is sorted by `le a b := !lt b a`. -/
theorem pairwise_insertionSort (hasymm : ∀ a b, lt a b → lt b a = false)
    (htrans : ∀ a b c, lt b a = false → lt c b = false → lt c a = false) (xs : Array α) :
    (insertionSort lt xs).toList.Pairwise (fun a b ↦ lt b a = false) := by
  rw [insertionSort_toList, List.pairwise_reverse]
  unfold bubbleAll
  suffices ∀ r : List α, r.Pairwise (fun a b ↦ lt a b = false) →
      (xs.toList.foldl (fun r x ↦ bubble lt x r) r).Pairwise (fun a b ↦ lt a b = false) by
    exact this [] List.Pairwise.nil
  induction xs.toList with
  | nil => exact fun _ h ↦ h
  | cons x l ih => exact fun r h ↦ ih _ (bubble_pairwise hasymm htrans x r h)

end NativeVm.Equiv
