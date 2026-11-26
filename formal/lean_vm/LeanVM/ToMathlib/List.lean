/-
  LeanVM.ToMathlib.List

  General `List` lemmas Mathlib does not state, one home for each, in Mathlib's namespace and naming.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.GetD

namespace List

public section

variable {α M : Type*}

/-! ## Entries -/

theorem getD_map_range (f : ℕ → α) {n i : ℕ} (h : i < n) {d : α} :
    ((range n).map f).getD i d = f i := by
  simp [getD_eq_getElem?_getD, h]

theorem getD_drop (l : List α) (a i : ℕ) (d : α) : (l.drop a).getD i d = l.getD (a + i) d := by
  simp only [getD_eq_getElem?_getD, getElem?_drop]

theorem getD_toArray (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, getD_eq_getElem?_getD]

theorem getD_mem {l : List α} {i : ℕ} {d : α} (h : i < l.length) : l.getD i d ∈ l := by
  rw [getD_eq_getElem _ _ h]; exact getElem_mem _

theorem getD_mem_or (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  rcases Nat.lt_or_ge i l.length with h | h
  · exact .inl (getD_mem h)
  · exact .inr (getD_eq_default _ _ h)

theorem map_range_getD {β : Type*} (l : List α) (d : α) (f : α → β) :
    (range l.length).map (fun i ↦ f (l.getD i d)) = l.map f := by
  apply ext_getElem (by simp)
  intro i h1 h2
  simp only [getElem_map, getElem_range]
  rw [getD_eq_getElem _ _ (by simpa using h1)]

theorem flatMap_range_getD {β : Type*} (f : α → List β) (d : α) (l : List α) :
    (range l.length).flatMap (fun i ↦ f (l.getD i d)) = l.flatMap f := by
  have h := map_range_getD l d id
  simp only [id_eq, map_id] at h
  rw [← flatMap_map, h]

/-- `2n` entries, two at a time. -/
theorem map_range_two_mul (f : ℕ → α) : ∀ n : ℕ,
    (range (2 * n)).map f = (range n).flatMap fun i ↦ [f (2 * i), f (2 * i + 1)]
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, range_add, map_append, map_range_two_mul f n,
      range_succ (n := n), flatMap_append]
    simp [range_succ]

/-! ## Running maxima -/

/-- A running maximum bounds its start and every element. -/
theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], _ => ⟨Nat.le_refl _, by simp⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨Nat.le_trans (Nat.le_max_left a y) h1, fun x hx ↦ ?_⟩
    rcases mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right a x) h1
    · exact h2 x hx

theorem foldl_max_le (M : ℕ) : ∀ (l : List ℕ) (a : ℕ), a ≤ M → (∀ x ∈ l, x ≤ M) → l.foldl max a ≤ M
  | [], _, h, _ => h
  | x :: l, _, h, hl => foldl_max_le M l _ (Nat.max_le.2 ⟨h, hl x mem_cons_self⟩) fun y hy ↦
      hl y (mem_cons_of_mem _ hy)

/-- A running maximum is its start or an element. -/
theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => .inl rfl
  | y :: l, a => by
    rcases foldl_max_mem l (max a y) with h | h
    · simp only [foldl_cons, h]
      rcases Nat.le_total a y with hay | hay
      · exact .inr (by rw [Nat.max_eq_right hay]; exact mem_cons_self)
      · exact .inl (Nat.max_eq_left hay)
    · exact .inr (mem_cons_of_mem _ h)

/-! ## Folds as sums and products -/

theorem foldl_mul_eq_mul_prod [Monoid M] (l : List M) (a : M) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [foldl_cons, ih, prod_cons, mul_assoc]

theorem foldl_add_eq_add_sum [AddMonoid M] (l : List M) (a : M) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [foldl_cons, ih, sum_cons, add_assoc]

theorem foldl_add_eq_add_sum_map [AddMonoid M] (f : α → M) (l : List α) (a : M) :
    l.foldl (fun acc x ↦ acc + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [foldl_cons, ih, map_cons, sum_cons, add_assoc]

theorem sum_flatMap [AddMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [flatMap_cons, sum_append, ih, map_cons, sum_cons]

end

end List
