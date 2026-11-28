/-
  LeanVM.Guest.B1.Stack.Offsets

  The statement's `stackOffsets` in closed form: a block's offset is the sizes of the blocks placed
  before it.
-/

module

public import Statement.Verifier.Layout
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# `stackOffsets`, in closed form

`stackOffsets sizes` sorts the blocks by size down, then by index, and lays them end to end. Block
`j` comes before block `i` (`StkBefore`) when it is larger, or as large and of a smaller index;
`stackOffsets_closed`: block `i`'s offset is the sum of `2^size` over the blocks before it, and the
log is `log2Ceil` of the sum over all blocks.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Protocol.Verifier

@[expose] public section

/-- Block `j` is placed before block `i`. -/
def StkBefore (sz : ℕ → ℕ) (j i : ℕ) : Prop := sz i < sz j ∨ (sz j = sz i ∧ j < i)

instance (sz : ℕ → ℕ) (j i : ℕ) : Decidable (StkBefore sz j i) := by
  unfold StkBefore; infer_instance

/-- The sum of `2^size` over the blocks before `i`, of `n`. -/
def stkBeforeSum (sz : ℕ → ℕ) (n i : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range n).filter (fun j ↦ StkBefore sz j i), 2 ^ sz j

/-! ## The fold -/

/-- The fold `stackOffsets` runs over its order. -/
def stkStep (w : ℕ → ℕ) (acc : List ℕ × ℕ) (i : ℕ) : List ℕ × ℕ := (acc.1.set i acc.2, acc.2 + w i)

theorem stkFold_snd (w : ℕ → ℕ) : ∀ (l : List ℕ) (acc : List ℕ × ℕ),
    (l.foldl (stkStep w) acc).2 = acc.2 + (l.map w).sum
  | [], _ => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, stkFold_snd w l, List.map_cons, List.sum_cons]
    simp [stkStep]; ring

theorem stkFold_length (w : ℕ → ℕ) : ∀ (l : List ℕ) (acc : List ℕ × ℕ),
    (l.foldl (stkStep w) acc).1.length = acc.1.length
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.foldl_cons, stkFold_length w l]; simp [stkStep]

/-- **The fold's entries**: an element `i` of a list without repeats, its indices below the
vector's length, gets the start plus the weights before it. -/
theorem stkFold_fst (w : ℕ → ℕ) : ∀ (l : List ℕ) (acc : List ℕ × ℕ), l.Nodup →
    (∀ x ∈ l, x < acc.1.length) → ∀ i ∈ l,
      (l.foldl (stkStep w) acc).1.getD i 0 = acc.2 + ((l.takeWhile (· ≠ i)).map w).sum
  | [], _, _, _, i, hi => absurd hi (by simp)
  | x :: l, acc, hnd, hlt, i, hi => by
    rw [List.foldl_cons]
    have hnd' := (List.nodup_cons.1 hnd)
    by_cases hix : i = x
    · subst hix
      -- `i` is not in the rest: its entry stays the one just set
      have keep : ∀ (l : List ℕ) (acc : List ℕ × ℕ), i ∉ l →
          (l.foldl (stkStep w) acc).1.getD i 0 = acc.1.getD i 0 := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons y l ih =>
          intro acc hy
          rw [List.foldl_cons, ih _ (fun h ↦ hy (List.mem_cons_of_mem _ h))]
          simp only [stkStep]
          have : i ≠ y := fun h ↦ hy (h ▸ List.mem_cons_self)
          simp [List.getD_eq_getElem?_getD, Ne.symm this]
      rw [keep l _ hnd'.1]
      have hl := hlt i List.mem_cons_self
      simp [stkStep, List.getD_eq_getElem?_getD, hl]
    · have hi' : i ∈ l := (List.mem_cons.1 hi).resolve_left hix
      rw [stkFold_fst w l _ hnd'.2 (fun y hy ↦ by
        simp only [stkStep, List.length_set]; exact hlt y (List.mem_cons_of_mem _ hy)) i hi']
      simp only [stkStep, List.takeWhile_cons, ne_eq, Ne.symm hix, not_false_eq_true,
        decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      ring

/-! ## The order -/

/-- `stackOffsets`' comparator. -/
def stkCmp (sz : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (sz j < sz i) || (decide (sz i = sz j) && decide (i ≤ j))

theorem stkCmp_trans (sz : ℕ → ℕ) (a b c : ℕ) (h1 : stkCmp sz a b) (h2 : stkCmp sz b c) :
    stkCmp sz a c := by
  simp only [stkCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem stkCmp_total (sz : ℕ → ℕ) (a b : ℕ) : stkCmp sz a b || stkCmp sz b a := by
  simp only [stkCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem stkCmp_antisymm {sz : ℕ → ℕ} {a b : ℕ} (h1 : stkCmp sz a b) (h2 : stkCmp sz b a) : a = b := by
  simp only [stkCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem stkBefore_iff {sz : ℕ → ℕ} {j i : ℕ} : StkBefore sz j i ↔ j ≠ i ∧ stkCmp sz j i := by
  by_cases h : j = i
  · subst h; simp [StkBefore]
  · simp only [StkBefore, stkCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-- In a list sorted by the comparator, without repeats and holding every block, the blocks before
`i` are those `StkBefore` it. -/
theorem takeWhile_sorted {sz : ℕ → ℕ} {n : ℕ} {l : List ℕ} (hs : l.Pairwise (stkCmp sz · ·))
    (hnd : l.Nodup) (hall : ∀ j, j ∈ l ↔ j < n) {i : ℕ} (hi : i ∈ l) :
    (l.takeWhile (· ≠ i)).toFinset = (Finset.range n).filter (fun j ↦ StkBefore sz j i) := by
  obtain ⟨l1, l2, rfl, hi1⟩ : ∃ l1 l2, l = l1 ++ i :: l2 ∧ i ∉ l1 := by
    obtain ⟨l1, l2, h⟩ := List.append_of_mem hi
    refine ⟨l1, l2, h, fun hm ↦ ?_⟩
    rw [h] at hnd
    exact (List.nodup_append.1 hnd).2.2 i hm i List.mem_cons_self rfl
  have htw : (l1 ++ i :: l2).takeWhile (· ≠ i) = l1 := by
    rw [List.takeWhile_append_of_pos (fun x hx ↦ by
      simp only [ne_eq, decide_eq_true_eq]; exact fun h ↦ hi1 (h ▸ hx))]
    simp
  rw [htw]
  ext j
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range, stkBefore_iff]
  rw [List.pairwise_append, List.pairwise_cons] at hs
  constructor
  · intro hj
    refine ⟨(hall j).1 (List.mem_append_left _ hj), fun h ↦ hi1 (h ▸ hj), hs.2.2 j hj i List.mem_cons_self⟩
  · rintro ⟨hjn, hne, hc⟩
    rcases List.mem_append.1 ((hall j).2 hjn) with h | h
    · exact h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h hne
      · exact absurd (stkCmp_antisymm hc (hs.2.1.1 j h)) hne

theorem sum_toFinset {l : List ℕ} (hnd : l.Nodup) (w : ℕ → ℕ) :
    (l.map w).sum = ∑ j ∈ l.toFinset, w j := by
  rw [List.sum_toFinset w hnd]

/-- **`stackOffsets` in closed form**: block `i`'s offset is the sum of `2^size` over the blocks
before it, and the log is `log2Ceil` of the sum over all. -/
theorem stackOffsets_closed (sizes : List ℕ) :
    (∀ i < sizes.length, (stackOffsets sizes).1.getD i 0 =
      stkBeforeSum (fun j ↦ sizes.getD j 0) sizes.length i) ∧
    (stackOffsets sizes).2 = log2Ceil (∑ j ∈ Finset.range sizes.length, 2 ^ sizes.getD j 0) := by
  set sz : ℕ → ℕ := fun j ↦ sizes.getD j 0 with hsz
  set n := sizes.length
  have hcmp : (fun i j ↦ decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j))) = stkCmp sz := rfl
  set order := (List.range n).mergeSort (stkCmp sz) with hord
  have hperm : order.Perm (List.range n) := List.mergeSort_perm _ _
  have hnd : order.Nodup := hperm.nodup_iff.2 List.nodup_range
  have hall : ∀ j, j ∈ order ↔ j < n := fun j ↦ by rw [hperm.mem_iff, List.mem_range]
  have hs : order.Pairwise (stkCmp sz · ·) :=
    List.pairwise_mergeSort (stkCmp_trans sz) (stkCmp_total sz) _
  have hso : stackOffsets sizes =
      ((order.foldl (stkStep fun i ↦ 2 ^ sz i) (List.replicate n 0, 0)).1,
        log2Ceil (order.foldl (stkStep fun i ↦ 2 ^ sz i) (List.replicate n 0, 0)).2) := by
    simp only [stackOffsets, hcmp]; rfl
  rw [hso]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [stkFold_fst _ order _ hnd (fun x hx ↦ by simpa using (hall x).1 hx) i ((hall i).2 hi),
      sum_toFinset (hnd.sublist (List.takeWhile_sublist _)), takeWhile_sorted hs hnd hall ((hall i).2 hi)]
    simp [stkBeforeSum]
  · have hset : order.toFinset = Finset.range n := by ext j; simp [hall]
    rw [stkFold_snd, sum_toFinset hnd, zero_add, hset]

end
end LeanVM.Guest.B1.Stack
