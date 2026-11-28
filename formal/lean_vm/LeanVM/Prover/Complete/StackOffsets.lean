/-
  LeanVM.Prover.Complete.StackOffsets

  `stack_offsets`' blocks are aligned, disjoint and inside the stack; writing disjoint blocks into
  an array leaves each block where it was written.
-/

module

public import LeanVM.Facts.Stack

/-!
# The stack's blocks

`stackOffsets sizes` lays blocks of `2^size` words end to end, largest first
(`stack_offsets`, `multilinear.rs`). Each block's offset is the sum of the blocks before it, all at
least as large, so it is a multiple of its own size (`stackOffsets_dvd`); two blocks never overlap
(`stackOffsets_disjoint`); every block ends inside `2^log2Ceil total` words (`stackOffsets_le`).

`writeBlock A index col` writes `col` into `A` from `index` on, as the stack's assembly does
(`stackArray`); `getD_foldl_writeBlock`: blocks written one after another, pairwise disjoint and
inside the array, are each read back whole.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

/-! ## The offsets -/

/-- The fold of `stack_offsets` from `acc` over the order `l`. -/
private def placeFold (size : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) : List ℕ × ℕ :=
  l.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i)) acc

private theorem placeFold_spec (size : ℕ → ℕ) :
    ∀ (l : List ℕ) (acc : List ℕ × ℕ), l.Nodup →
      (placeFold size l acc).1.length = acc.1.length ∧
      (∀ i, i ∉ l → (placeFold size l acc).1.getD i 0 = acc.1.getD i 0) ∧
      (∀ i ∈ l, i < acc.1.length →
        (placeFold size l acc).1.getD i 0 =
          acc.2 + ((l.take (l.idxOf i)).map fun j ↦ 2 ^ size j).sum)
  | [], acc, _ => by simp [placeFold]
  | x :: l, acc, hnd => by
    have hx : x ∉ l := (List.nodup_cons.mp hnd).1
    obtain ⟨h1, h2, h3⟩ := placeFold_spec size l (acc.1.set x acc.2, acc.2 + 2 ^ size x)
      (List.nodup_cons.mp hnd).2
    have hstep : placeFold size (x :: l) acc =
        placeFold size l (acc.1.set x acc.2, acc.2 + 2 ^ size x) := rfl
    rw [hstep]
    refine ⟨by simp [h1], fun i hi ↦ ?_, fun i hi hlt ↦ ?_⟩
    · have hix : i ≠ x := fun h ↦ hi (h ▸ List.mem_cons_self)
      rw [h2 i fun h ↦ hi (List.mem_cons_of_mem _ h)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
      simp [Ne.symm hix]
    · rcases List.mem_cons.mp hi with rfl | hil
      · rw [h2 i hx]
        simp [List.getD_eq_getElem?_getD, hlt]
      · have hix : i ≠ x := fun h ↦ hx (h ▸ hil)
        rw [h3 i hil (by simpa using hlt), List.idxOf_cons_ne _ (Ne.symm hix)]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega

/-- The comparator of `stack_offsets`' sort: size down, then index. -/
private def offsetsLe (size : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))

private theorem offsetsOrder_sorted (size : ℕ → ℕ) (n : ℕ) :
    ((List.range n).mergeSort (offsetsLe size)).Pairwise fun a b ↦ offsetsLe size a b := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [offsetsLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
    omega
  · intro a b
    simp only [offsetsLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    omega

/-- What `stack_offsets` computes, in terms of the order it places the blocks in. -/
private theorem stackOffsets_eq (sizes : List ℕ) :
    stackOffsets sizes = ((placeFold (fun i ↦ sizes.getD i 0)
      ((List.range sizes.length).mergeSort (offsetsLe fun i ↦ sizes.getD i 0))
      (List.replicate sizes.length 0, 0)).1,
      log2Ceil (placeFold (fun i ↦ sizes.getD i 0)
      ((List.range sizes.length).mergeSort (offsetsLe fun i ↦ sizes.getD i 0))
      (List.replicate sizes.length 0, 0)).2) := rfl

private theorem placeFold_snd (size : ℕ → ℕ) :
    ∀ (l : List ℕ) (acc : List ℕ × ℕ),
      (placeFold size l acc).2 = acc.2 + (l.map fun j ↦ 2 ^ size j).sum
  | [], _ => by simp [placeFold]
  | x :: l, acc => by
    have := placeFold_snd size l (acc.1.set x acc.2, acc.2 + 2 ^ size x)
    simp only [placeFold, List.foldl_cons] at this ⊢
    rw [this]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- In a list without repeats, the entries before `i` sum to less than those before a later
`j` by at least `i`'s own. -/
private theorem take_idxOf_sum_le {f : ℕ → ℕ} {l : List ℕ} {i j : ℕ} (hi : i ∈ l)
    (hij : l.idxOf i < l.idxOf j) :
    ((l.take (l.idxOf i)).map f).sum + f i ≤ ((l.take (l.idxOf j)).map f).sum := by
  have hlt : l.idxOf i < l.length := List.idxOf_lt_length_iff.mpr hi
  have hget : l[l.idxOf i] = i := List.getElem_idxOf hlt
  have hsplit : l.take (l.idxOf j) =
      l.take (l.idxOf i) ++ l[l.idxOf i] :: (l.take (l.idxOf j)).drop (l.idxOf i + 1) := by
    conv_lhs => rw [← List.take_append_drop (l.idxOf i) (l.take (l.idxOf j))]
    rw [List.take_take, Nat.min_eq_left hij.le]
    congr 1
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp [List.getElem_take]
  rw [hsplit, hget]
  simp

/-- **The blocks' facts**: every offset is a multiple of its block's size and its block ends inside
`2^log2Ceil total`, and two blocks are disjoint. -/
theorem stackOffsets_spec (sizes : List ℕ) :
    (stackOffsets sizes).1.length = sizes.length ∧
    (∀ i < sizes.length, 2 ^ sizes.getD i 0 ∣ (stackOffsets sizes).1.getD i 0 ∧
      (stackOffsets sizes).1.getD i 0 + 2 ^ sizes.getD i 0 ≤ 2 ^ (stackOffsets sizes).2) ∧
    (∀ i < sizes.length, ∀ j < sizes.length, i ≠ j →
      (stackOffsets sizes).1.getD i 0 + 2 ^ sizes.getD i 0 ≤ (stackOffsets sizes).1.getD j 0 ∨
      (stackOffsets sizes).1.getD j 0 + 2 ^ sizes.getD j 0 ≤ (stackOffsets sizes).1.getD i 0) := by
  set size := fun i ↦ sizes.getD i 0
  set order := (List.range sizes.length).mergeSort (offsetsLe size)
  have hperm : order.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hnd : order.Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hmem : ∀ i, i ∈ order ↔ i < sizes.length := fun i ↦ by
    rw [hperm.mem_iff, List.mem_range]
  have hsorted : order.Pairwise fun a b ↦ offsetsLe size a b := offsetsOrder_sorted size sizes.length
  obtain ⟨hlen, -, hval⟩ := placeFold_spec size order (List.replicate sizes.length 0, 0) hnd
  have htot := placeFold_snd size order (List.replicate sizes.length 0, 0)
  rw [stackOffsets_eq]
  simp only [List.length_replicate] at hlen hval
  have hoff : ∀ i < sizes.length, (placeFold size order (List.replicate sizes.length 0, 0)).1.getD i 0
      = ((order.take (order.idxOf i)).map fun j ↦ 2 ^ size j).sum := fun i hi ↦ by
    rw [hval i ((hmem i).mpr hi) hi]; simp
  -- Every block before `i` is at least as large.
  have hbefore : ∀ i ∈ order, ∀ j ∈ order.take (order.idxOf i), size i ≤ size j := by
    intro i hi j hj
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hj
    have hm' : m < order.idxOf i := by rw [List.length_take] at hm; omega
    have hlt : order.idxOf i < order.length := List.idxOf_lt_length_iff.mpr hi
    have := List.pairwise_iff_getElem.mp hsorted m (order.idxOf i) (by omega) hlt hm'
    rw [List.getElem_idxOf hlt] at this
    simp only [List.getElem_take, offsetsLe, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at this ⊢
    omega
  have hsum_le : ∀ i ∈ order, ((order.take (order.idxOf i)).map fun j ↦ 2 ^ size j).sum +
      2 ^ size i ≤ (order.map fun j ↦ 2 ^ size j).sum := by
    intro i hi
    have hlt : order.idxOf i < order.length := List.idxOf_lt_length_iff.mpr hi
    conv_rhs => rw [← List.take_append_drop (order.idxOf i) order]
    rw [List.map_append, List.sum_append, List.drop_eq_getElem_cons hlt, List.getElem_idxOf hlt]
    simp only [List.map_cons, List.sum_cons]
    omega
  refine ⟨hlen, fun i hi ↦ ⟨?_, ?_⟩, fun i hi j hj hij ↦ ?_⟩
  · rw [hoff i hi]
    apply List.dvd_sum
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact Nat.pow_dvd_pow 2 (hbefore i ((hmem i).mpr hi) j hj)
  · rw [hoff i hi, htot]
    refine le_trans (hsum_le i ((hmem i).mpr hi)) ?_
    simp only [zero_add]
    exact (log2Ceil_le_iff _ _).mp le_rfl
  · rw [hoff i hi, hoff j hj]
    have hi' := (hmem i).mpr hi
    have hj' := (hmem j).mpr hj
    have hne : order.idxOf i ≠ order.idxOf j := fun h ↦ hij (by
      rw [← List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hi'),
        ← List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hj')]
      simp [h])
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl (take_idxOf_sum_le hi' h)
    · exact Or.inr (take_idxOf_sum_le hj' h)

/-! ## Writing blocks -/

/-- Write `col` into `A` from `index` on (`stackArray`'s loop body). -/
def writeBlock (A : Array K) (index : ℕ) (col : Array K) : Array K :=
  Nat.fold col.size (fun i h stack ↦ stack.set! (index + i) col[i]) A

/-- The loop of `writeBlock`, its first `n` words. -/
def writeN (A : Array K) (index : ℕ) (col : Array K) (n : ℕ) : Array K :=
  Nat.fold n (fun i _ stack ↦ stack.set! (index + i) (col.getD i 0)) A

private theorem writeN_spec (A : Array K) (index : ℕ) (col : Array K) :
    ∀ n, (writeN A index col n).size = A.size ∧ ∀ y, (writeN A index col n).getD y 0 =
      if index ≤ y ∧ y < index + n ∧ y < A.size then col.getD (y - index) 0 else A.getD y 0
  | 0 => ⟨by simp [writeN], fun y ↦ by simp only [writeN, Nat.fold_zero]; split <;> [omega; rfl]⟩
  | n + 1 => by
    obtain ⟨hs, hg⟩ := writeN_spec A index col n
    have hstep : writeN A index col (n + 1) =
        (writeN A index col n).set! (index + n) (col.getD n 0) := by
      simp [writeN, Nat.fold_succ]
    rw [hstep]
    refine ⟨by simp [hs], fun y ↦ ?_⟩
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
      hs] at hg ⊢
    by_cases hy : index + n = y
    · subst hy
      by_cases hb : index + n < A.size <;> simp [hb]
    · simp only [hy, ↓reduceIte, hg y]
      split_ifs <;> first | rfl | omega

theorem writeBlock_eq (A : Array K) (index : ℕ) (col : Array K) :
    writeBlock A index col = writeN A index col col.size := by
  unfold writeBlock writeN
  exact congrArg (fun f ↦ Nat.fold col.size f A)
    (funext fun i ↦ funext fun h ↦ funext fun s ↦ by simp [Array.getD_eq_getD_getElem?, h])

/-- **A written block**: `writeBlock` keeps the size, and reads `col` on its block inside the
array, `A` elsewhere. -/
theorem writeBlock_spec (A : Array K) (index : ℕ) (col : Array K) :
    (writeBlock A index col).size = A.size ∧ ∀ y, (writeBlock A index col).getD y 0 =
      if index ≤ y ∧ y < index + col.size ∧ y < A.size then col.getD (y - index) 0
      else A.getD y 0 := by
  rw [writeBlock_eq]
  exact writeN_spec A index col col.size

/-- Two blocks `(index, words)` that do not overlap. -/
def BlocksDisjoint (a b : ℕ × Array K) : Prop := a.1 + a.2.size ≤ b.1 ∨ b.1 + b.2.size ≤ a.1

/-- Blocks written one after another. -/
def writeBlocks (A : Array K) (ws : List (ℕ × Array K)) : Array K :=
  ws.foldl (fun A w ↦ writeBlock A w.1 w.2) A

theorem size_writeBlocks : ∀ (A : Array K) (ws : List (ℕ × Array K)),
    (writeBlocks A ws).size = A.size
  | _, [] => rfl
  | A, w :: ws => by
    rw [show writeBlocks A (w :: ws) = writeBlocks (writeBlock A w.1 w.2) ws from rfl,
      size_writeBlocks, (writeBlock_spec A w.1 w.2).1]

/-- A word no block covers keeps its value. -/
theorem getD_writeBlocks_of_not_mem : ∀ (A : Array K) (ws : List (ℕ × Array K)) (y : ℕ),
    (∀ w ∈ ws, ¬ (w.1 ≤ y ∧ y < w.1 + w.2.size)) → (writeBlocks A ws).getD y 0 = A.getD y 0
  | _, [], _, _ => rfl
  | A, w :: ws, y, h => by
    rw [show writeBlocks A (w :: ws) = writeBlocks (writeBlock A w.1 w.2) ws from rfl,
      getD_writeBlocks_of_not_mem _ ws y fun w' hw' ↦ h w' (List.mem_cons_of_mem _ hw'),
      (writeBlock_spec A w.1 w.2).2 y]
    have := h w List.mem_cons_self
    split_ifs with h' <;> [exact absurd ⟨h'.1, h'.2.1⟩ this; rfl]

/-- **Each written block reads back whole**, when the blocks are pairwise disjoint and it lies
inside the array. -/
theorem getD_writeBlocks : ∀ (A : Array K) (ws : List (ℕ × Array K)),
    ws.Pairwise BlocksDisjoint → ∀ w ∈ ws, w.1 + w.2.size ≤ A.size → ∀ i < w.2.size,
      (writeBlocks A ws).getD (w.1 + i) 0 = w.2.getD i 0
  | _, [], _, _, hw, _, _, _ => absurd hw List.not_mem_nil
  | A, w₀ :: ws, hd, w, hw, hin, i, hi => by
    rw [show writeBlocks A (w₀ :: ws) = writeBlocks (writeBlock A w₀.1 w₀.2) ws from rfl]
    have hd' := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [getD_writeBlocks_of_not_mem _ ws _ fun w' hw' ↦ by
          rcases hd'.1 w' hw' with h | h <;> omega,
        (writeBlock_spec A w.1 w.2).2]
      have hc : w.1 ≤ w.1 + i ∧ w.1 + i < w.1 + w.2.size ∧ w.1 + i < A.size := by omega
      simp [hc]
    · exact getD_writeBlocks _ ws hd'.2 w hw (by rw [(writeBlock_spec A w₀.1 w₀.2).1]; exact hin) i hi

end LeanVM.Protocol.Verifier

end
