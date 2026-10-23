/-
  LeanVM.Arithmetization.Completeness.Balance

  The list arithmetic behind the balance of the three channel pairs: the read counters, the chain
  lemma, and two permutations.
-/

module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Range
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# Chain balance

The memory pair and the bytecode pair balance by the same argument. Seed every cell with its first
message and finalize it with its last; each read of a cell pulls the cell's message with its current
count and pushes the message with the next. If the reads of each cell number its messages in order,
`0`, `1`, `2`, …, the pushes (the seeds and one per read) and the pulls (the finalizes and one per
read) are the same multiset: that is `chain_balance`, a `List.Perm` over any message type, stated
for a nodup list of cells `keys`, a message `mk cell n` for the cell's `n`-th message, and a
sequence of reads `L` of cells in `keys`.

`readExps s L` is the number each read of `L` gets, from the counters `s` of the reads so far, and
`readBump s L` the counters after `L`; they split over a concatenation
(`readExps_append`, `readBump_append`), so a sequence of rows is one sequence of reads. The proof
is one induction on `L`: reading a cell swaps its current message for the next in the list of
current messages (`swap_perm`), and a swap is a push and a pull.

`mapIdx_eq_zipWith` turns a row's reads, indexed by position, into the zip with their numbers;
`shift_perm` is the state pair's chain, `r₀` and the successors of the run's states against the
last state and the run's states; `regroup_perm` regroups a list by a key into a nodup list of
keys, how the rows of the six tables are the rows of the run in another order.

## Wrong readings excluded

* The balance is a permutation, not a sum in the field: a cell read
  twice with the same number is not balanced, and the test says so.
* The numbers are the reads so far of *the cell*, never of the whole sequence: two cells read in
  turn each start at `0`.
-/

open scoped List

namespace LeanVM.Arithmetization

variable {ι α : Type} [DecidableEq ι]

/-! ## The read counters -/

/-- The number each read of a sequence gets: the reads of the same cell before it, from the
counters `s` of the reads so far. -/
def readExps (s : ι → ℕ) : List ι → List ℕ
  | [] => []
  | a :: rest => s a :: readExps (Function.update s a (s a + 1)) rest

/-- The counters after a sequence of reads. -/
def readBump (s : ι → ℕ) : List ι → (ι → ℕ)
  | [] => s
  | a :: rest => readBump (Function.update s a (s a + 1)) rest

/-- Every read gets a number. -/
theorem readExps_length (s : ι → ℕ) (l : List ι) : (readExps s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [readExps, ih]

/-- The numbers of a concatenation of reads: those of the first, then those of the second from the
counters the first leaves. -/
theorem readExps_append (s : ι → ℕ) (l₁ l₂ : List ι) :
    readExps s (l₁ ++ l₂) = readExps s l₁ ++ readExps (readBump s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a l ih => simp [readExps, readBump, ih]

/-- The counters after a concatenation of reads. -/
theorem readBump_append (s : ι → ℕ) (l₁ l₂ : List ι) :
    readBump s (l₁ ++ l₂) = readBump (readBump s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a l ih => simp [readBump, ih]

/-! ## The chain lemma -/

/-- Replacing one cell's current message by the next is a swap with a push. -/
theorem swap_perm (keys : List ι) (hnd : keys.Nodup) (mk : ι → ℕ → α) (s : ι → ℕ) {b : ι}
    (hb : b ∈ keys) :
    ((keys.map fun a ↦ mk a (s a)) ++ [mk b (s b + 1)]).Perm
      (mk b (s b) :: keys.map fun a ↦ mk a (Function.update s b (s b + 1) a)) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb
  obtain ⟨-, hn2, hdisj⟩ := List.nodup_append.mp hnd
  have hb1 : b ∉ l₁ := fun h ↦ hdisj b h b List.mem_cons_self rfl
  have hb2 : b ∉ l₂ := (List.nodup_cons.mp hn2).1
  have e1 : l₁.map (fun a ↦ mk a (Function.update s b (s b + 1) a)) =
      l₁.map (fun a ↦ mk a (s a)) :=
    List.map_congr_left fun a ha ↦ by
      have hne : a ≠ b := fun h ↦ hb1 (h ▸ ha)
      rw [Function.update_of_ne hne]
  have e2 : l₂.map (fun a ↦ mk a (Function.update s b (s b + 1) a)) =
      l₂.map (fun a ↦ mk a (s a)) :=
    List.map_congr_left fun a ha ↦ by
      have hne : a ≠ b := fun h ↦ hb2 (h ▸ ha)
      rw [Function.update_of_ne hne]
  simp only [List.map_append, List.map_cons, Function.update_self, e1, e2]
  calc (l₁.map fun a ↦ mk a (s a)) ++ mk b (s b) :: (l₂.map fun a ↦ mk a (s a)) ++
        [mk b (s b + 1)]
      = (l₁.map fun a ↦ mk a (s a)) ++
          mk b (s b) :: ((l₂.map fun a ↦ mk a (s a)) ++ [mk b (s b + 1)]) := by simp
    _ ~ mk b (s b) :: ((l₁.map fun a ↦ mk a (s a)) ++
          ((l₂.map fun a ↦ mk a (s a)) ++ [mk b (s b + 1)])) := List.perm_middle
    _ ~ mk b (s b) :: ((l₁.map fun a ↦ mk a (s a)) ++
          mk b (s b + 1) :: (l₂.map fun a ↦ mk a (s a))) :=
        List.Perm.cons _ (List.Perm.append_left _ (List.perm_append_singleton _ _))

/-- **The chain lemma.** Seeding every cell with its first message and pushing the message of each
read is a permutation of finalizing every cell with its last message and pulling the message of
each read, when the reads of each cell number its messages in order. -/
theorem chain_balance (keys : List ι) (hnd : keys.Nodup) (mk : ι → ℕ → α) :
    ∀ (L : List ι), (∀ a ∈ L, a ∈ keys) → ∀ s : ι → ℕ,
      ((keys.map fun a ↦ mk a (s a)) ++
        List.zipWith (fun a e ↦ mk a (e + 1)) L (readExps s L)).Perm
      ((keys.map fun a ↦ mk a (readBump s L a)) ++
        List.zipWith (fun a e ↦ mk a e) L (readExps s L)) := by
  intro L
  induction L with
  | nil => intro _ s; exact List.Perm.refl _
  | cons b L ih =>
    intro hL s
    have hb : b ∈ keys := hL b List.mem_cons_self
    have ih' := ih (fun a ha ↦ hL a (List.mem_cons_of_mem _ ha)) (Function.update s b (s b + 1))
    simp only [readExps, readBump, List.zipWith_cons_cons]
    have hs := swap_perm keys hnd mk s hb
    calc ((keys.map fun a ↦ mk a (s a)) ++ (mk b (s b + 1) ::
          List.zipWith (fun a e ↦ mk a (e + 1)) L (readExps (Function.update s b (s b + 1)) L)))
        = ((keys.map fun a ↦ mk a (s a)) ++ [mk b (s b + 1)]) ++
            List.zipWith (fun a e ↦ mk a (e + 1)) L
              (readExps (Function.update s b (s b + 1)) L) := by
          simp
      _ ~ (mk b (s b) :: keys.map fun a ↦ mk a (Function.update s b (s b + 1) a)) ++
            List.zipWith (fun a e ↦ mk a (e + 1)) L
              (readExps (Function.update s b (s b + 1)) L) :=
          List.Perm.append_right _ hs
      _ = mk b (s b) :: ((keys.map fun a ↦ mk a (Function.update s b (s b + 1) a)) ++
            List.zipWith (fun a e ↦ mk a (e + 1)) L
              (readExps (Function.update s b (s b + 1)) L)) := by
          simp
      _ ~ mk b (s b) :: ((keys.map fun a ↦ mk a (readBump (Function.update s b (s b + 1)) L a)) ++
            List.zipWith (fun a e ↦ mk a e) L (readExps (Function.update s b (s b + 1)) L)) :=
          List.Perm.cons _ ih'
      _ ~ ((keys.map fun a ↦ mk a (readBump (Function.update s b (s b + 1)) L a)) ++
            (mk b (s b) :: List.zipWith (fun a e ↦ mk a e) L
              (readExps (Function.update s b (s b + 1)) L))) :=
          List.perm_middle.symm

/-! ## Rows, and the state pair -/

/-- Indexing the numbers by position is the zip with them. -/
theorem mapIdx_eq_zipWith {γ : Type} (F : α → ℕ → γ) (es : List ℕ) (l : List α)
    (h : es.length = l.length) :
    l.mapIdx (fun j a ↦ F a (es.getD j 0)) = List.zipWith F l es := by
  induction l generalizing es with
  | nil => rfl
  | cons a l ih =>
    cases es with
    | nil => simp at h
    | cons e es =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.mapIdx_cons, List.zipWith_cons_cons, List.getD_cons_zero]
      congr 1
      simpa [List.getD_cons_succ] using ih es h

/-- A rotation of a list of values is a permutation: the first value and the successors of the
rest are the last value and the rest. -/
theorem shift_perm {β : Type} (f : ℕ → β) (n : ℕ) :
    (f 0 :: (List.range n).map fun k ↦ f (k + 1)).Perm (f n :: (List.range n).map f) := by
  have h1 : f 0 :: (List.range n).map (fun k ↦ f (k + 1)) = (List.range (n + 1)).map f := by
    rw [List.range_succ_eq_map]; simp
  have h2 : (List.range n).map f ++ [f n] = (List.range (n + 1)).map f := by
    rw [List.range_succ]; simp
  rw [h1, ← h2]
  exact List.perm_append_singleton _ _

/-- Partitioning a list by a key into the cells of a nodup list of keys, in order, is a
permutation of it. -/
theorem regroup_perm {β : Type} (ops : List ι) (key : β → ι) :
    ∀ (l : List β), ops.Nodup → (∀ x ∈ l, key x ∈ ops) →
      (ops.flatMap fun o ↦ l.filter fun x ↦ key x = o).Perm l := by
  induction ops with
  | nil =>
    intro l _ h
    cases l with
    | nil => exact List.Perm.refl _
    | cons x l => exact absurd (h x List.mem_cons_self) (by simp)
  | cons o ops ih =>
    intro l hnd hl
    obtain ⟨ho, hops⟩ := List.nodup_cons.mp hnd
    have hrest : (ops.flatMap fun o' ↦ l.filter fun x ↦ key x = o') =
        ops.flatMap fun o' ↦ (l.filter fun x ↦ key x ≠ o).filter fun x ↦ key x = o' := by
      refine List.flatMap_congr fun o' ho' ↦ ?_
      rw [List.filter_filter]
      refine List.filter_congr fun x _ ↦ ?_
      by_cases h : key x = o'
      · have hne : o' ≠ o := fun h' ↦ ho (h' ▸ ho')
        simp [h, hne]
      · simp [h]
    simp only [List.flatMap_cons, hrest]
    have h2 := ih (l.filter fun x ↦ key x ≠ o) hops (by
      intro x hx
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      have := hl x hx1
      simp only [decide_eq_true_eq] at hx2
      simpa [hx2] using this)
    have h3 : (l.filter fun x ↦ key x = o) ++ (l.filter fun x ↦ key x ≠ o) |>.Perm l := by
      simpa [decide_not] using List.filter_append_perm (fun x ↦ decide (key x = o)) l
    exact (List.Perm.append_left _ h2).trans h3

end LeanVM.Arithmetization
