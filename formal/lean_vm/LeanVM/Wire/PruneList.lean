/-
  LeanVM.Wire.PruneList

  List facts the encoder's side of the round trip uses: `dedupByKey` keeps a sublist and commutes
  with maps along its key; a leaf's common zero prefix.
-/

module

public import LeanVM.Wire.Encoding

/-!
# List facts for the pruning

`dedupByKey` (`LeanVM.Wire.Encoding`) keeps a sublist of its input, a member of each key
it meets (`dedupByKey_sublist`, `exists_mem_dedupByKey`), and commutes with a map along its key
(`map_dedupByKey`). `takeWhile` of the zero words gives the leading zeros of a leaf
(`take_eq_replicate_of_le_takeWhile`, `getElem_ne_zero_of_takeWhile`).
-/

@[expose] public section

namespace LeanVM.Wire.PruneList

open LeanVM.Protocol.Compile

variable {α β γ : Type}

theorem dedupByKey_sublist [DecidableEq β] (key : α → β) :
    ∀ l : List α, (dedupByKey key l).Sublist l
  | [] => by simp [dedupByKey]
  | a :: rest => by
    have ih := dedupByKey_sublist key rest
    unfold dedupByKey
    split
    · exact List.Sublist.cons_cons a (List.nil_sublist _)
    · rename_i b kept heq
      rw [heq] at ih
      split
      · exact List.Sublist.cons_cons a (List.sublist_of_cons_sublist ih)
      · exact List.Sublist.cons_cons a ih

theorem mem_of_mem_dedupByKey [DecidableEq β] {key : α → β} {l : List α} {a : α}
    (h : a ∈ dedupByKey key l) : a ∈ l :=
  (dedupByKey_sublist key l).subset h

theorem exists_mem_dedupByKey [DecidableEq β] (key : α → β) :
    ∀ (l : List α), ∀ a ∈ l, ∃ b ∈ dedupByKey key l, key b = key a
  | [], a, h => by simp at h
  | c :: rest, a, h => by
    have ih := exists_mem_dedupByKey key rest
    unfold dedupByKey
    split
    · rename_i heq
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨a, by simp⟩
      · obtain ⟨b, hb, _⟩ := ih a h
        rw [heq] at hb
        simp at hb
    · rename_i b kept heq
      rcases List.mem_cons.1 h with rfl | h
      · split <;> exact ⟨a, by simp, rfl⟩
      · obtain ⟨d, hd, hkey⟩ := ih a h
        rw [heq] at hd
        split
        · rename_i hcb
          rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨c, by simp, hcb.trans hkey⟩
          · exact ⟨d, by simp [hd], hkey⟩
        · exact ⟨d, List.mem_cons_of_mem _ hd, hkey⟩

theorem dedupByKey_ne_nil [DecidableEq β] (key : α → β) {l : List α} (h : l ≠ []) :
    dedupByKey key l ≠ [] := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l h
  obtain ⟨b, hb, _⟩ := exists_mem_dedupByKey key l a ha
  exact List.ne_nil_of_mem hb

/-- `dedupByKey` along `key` then a map `g` is `dedupByKey` along `key'` after `g`, where `key`
factors through `g`. -/
theorem map_dedupByKey [DecidableEq β] {δ : Type} (key : α → β) (key' : δ → β)
    (g : α → δ) (hkey : ∀ a, key a = key' (g a)) :
    ∀ l : List α, (dedupByKey key l).map g = dedupByKey key' (l.map g)
  | [] => by simp [dedupByKey]
  | a :: rest => by
    have ih := map_dedupByKey key key' g hkey rest
    simp only [dedupByKey, List.map_cons]
    rw [← ih]
    split
    · rename_i heq
      rw [heq]
      rfl
    · rename_i b kept heq
      rw [heq]
      simp only [List.map_cons, hkey]
      split <;> rfl

/-- The first `n` words of a list whose `takeWhile` of the zero words has at least `n` words are
zero. -/
theorem take_eq_replicate_of_le_takeWhile {M : Type} [Zero M] [DecidableEq M] (l : List M) (n : ℕ)
    (hn : n ≤ (l.takeWhile fun word ↦ decide (word = 0)).length) :
    l.take n = List.replicate n 0 := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun word : M ↦ decide (word = 0)) (l := l)
  have htake : l.take n = (l.takeWhile fun word ↦ decide (word = 0)).take n := by
    conv_lhs => rw [← hsplit]
    exact List.take_append_of_le_length hn
  rw [htake, List.eq_replicate_iff]
  refine ⟨by simp [Nat.min_eq_left hn], fun b hb ↦ ?_⟩
  have hall := List.all_takeWhile (p := fun word : M ↦ decide (word = 0)) (l := l)
  rw [List.all_eq_true] at hall
  simpa using hall b (List.mem_of_mem_take hb)

/-- The leaf of `paddedLeaf`: a leaf with at least `n` leading zero words is its words after the
first `n`, padded back. -/
theorem replicate_append_drop {M : Type} [Zero M] [DecidableEq M] (l : List M) (n : ℕ)
    (hn : n ≤ (l.takeWhile fun word ↦ decide (word = 0)).length) :
    List.replicate n 0 ++ l.drop n = l := by
  rw [← take_eq_replicate_of_le_takeWhile l n hn, List.take_append_drop]

/-- The word after the leading zeros is nonzero. -/
theorem getD_ne_zero_of_takeWhile {M : Type} [Zero M] [DecidableEq M] (l : List M)
    (hlt : (l.takeWhile fun word ↦ decide (word = 0)).length < l.length) :
    l.getD (l.takeWhile fun word ↦ decide (word = 0)).length 0 ≠ 0 := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun word : M ↦ decide (word = 0)) (l := l)
  have hne : l.dropWhile (fun word ↦ decide (word = 0)) ≠ [] := by
    intro h
    rw [h, List.append_nil] at hsplit
    rw [hsplit] at hlt
    exact Nat.lt_irrefl _ hlt
  have hhead := List.head_dropWhile_not (fun word : M ↦ decide (word = 0)) (l := l) hne
  have key : ∀ t d : List M, (t ++ d)[t.length]? = d.head? := fun t d ↦ by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, ← List.head?_eq_getElem?]
  have hat := key (l.takeWhile fun word ↦ decide (word = 0))
    (l.dropWhile fun word ↦ decide (word = 0))
  rw [hsplit] at hat
  rw [List.getD_eq_getElem?_getD, hat, List.head?_eq_some_head hne]
  simpa using hhead

end LeanVM.Wire.PruneList

end
