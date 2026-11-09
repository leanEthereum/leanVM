/-
  LeanVM.Wire.UnpruneList

  List facts of the wire encoding: what `dedupByKey`, `distinctPositions` and `levelNodes` keep,
  the nodes one level up as the climb computes them, and `List.lookup` on keyed lists.
-/

module

public import LeanVM.Wire.Spec
import Mathlib.Data.Nat.Bitwise

/-!
# List facts of the wire encoding

`dedupByKey` keeps a member of each key, and nothing else; on a list sorted by `≤` it gives the
distinct members ascending (`pairwise_lt_dedupByKey_id`). Two strictly ascending lists with the
same members are equal (`eq_of_pairwise_lt_of_mem_iff`), the form every equation between node
lists below takes. `levelNodes positions (k + 1)` is the level-`k` nodes that are first children
(even, or without their sibling), each shifted once (`levelNodes_succ`): the parents
`climbLevel` hashes.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Protocol.Compile

public section

/-! ## `dedupByKey` -/

theorem dedupByKey_cons_eq {α β : Type} [DecidableEq β] (key : α → β) (a : α) (rest : List α) :
    ∃ t, dedupByKey key (a :: rest) = a :: t := by
  rw [dedupByKey]
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem mem_of_mem_dedupByKey {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ {l : List α} {x : α}, x ∈ dedupByKey key l → x ∈ l
  | [], x, hx => by simp [dedupByKey] at hx
  | a :: rest, x, hx => by
    rw [dedupByKey] at hx
    split at hx
    · simp_all
    · rename_i b kept heq
      have hsub : ∀ y ∈ b :: kept, y ∈ a :: rest := fun y hy ↦
        List.mem_cons_of_mem _ (mem_of_mem_dedupByKey key (heq ▸ hy))
      split at hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact hsub x (List.mem_cons_of_mem _ hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact hsub x hx

theorem exists_mem_dedupByKey {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ {l : List α} {a : α}, a ∈ l → ∃ b ∈ dedupByKey key l, key b = key a
  | [], a, ha => by simp at ha
  | c :: rest, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · obtain ⟨t, ht⟩ := dedupByKey_cons_eq key a rest
      exact ⟨a, by rw [ht]; exact List.mem_cons_self, rfl⟩
    · obtain ⟨b, hb, hkey⟩ := exists_mem_dedupByKey key ha
      rw [dedupByKey]
      split
      · rename_i heq
        rw [heq] at hb
        simp at hb
      · rename_i b' kept heq
        rw [heq] at hb
        split
        · rename_i hc
          rcases List.mem_cons.1 hb with rfl | hb
          · exact ⟨c, List.mem_cons_self, hc.trans hkey⟩
          · exact ⟨b, List.mem_cons_of_mem _ hb, hkey⟩
        · exact ⟨b, List.mem_cons_of_mem _ hb, hkey⟩

theorem mem_dedupByKey_id {α : Type} [DecidableEq α] {l : List α} {x : α} :
    x ∈ dedupByKey id l ↔ x ∈ l := by
  refine ⟨mem_of_mem_dedupByKey id, fun hx ↦ ?_⟩
  obtain ⟨b, hb, hkey⟩ := exists_mem_dedupByKey id hx
  exact (show b = x from hkey) ▸ hb

theorem map_dedupByKey {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ l : List α, (dedupByKey key l).map key = dedupByKey id (l.map key)
  | [] => rfl
  | a :: rest => by
    have ih := map_dedupByKey key rest
    rw [List.map_cons, dedupByKey, dedupByKey, ← ih]
    rcases dedupByKey key rest with _ | ⟨b, kept⟩
    · rfl
    · simp only [List.map_cons, id]
      split <;> rfl

theorem pairwise_lt_dedupByKey_id :
    ∀ {l : List ℕ}, l.Pairwise (· ≤ ·) → (dedupByKey id l).Pairwise (· < ·)
  | [], _ => by simp [dedupByKey]
  | a :: rest, hl => by
    have ih := pairwise_lt_dedupByKey_id hl.of_cons
    have hle : ∀ x ∈ dedupByKey id rest, a ≤ x := fun x hx ↦
      List.rel_of_pairwise_cons hl (mem_of_mem_dedupByKey id hx)
    rw [dedupByKey]
    split
    · simp
    · rename_i b kept heq
      rw [heq] at ih hle
      have hb : ∀ x ∈ kept, b < x := fun x hx ↦ List.rel_of_pairwise_cons ih hx
      split
      · rename_i hab
        simp only [id] at hab
        subst hab
        exact List.Pairwise.cons hb ih.of_cons
      · rename_i hab
        simp only [id] at hab
        have hab' : a < b := lt_of_le_of_ne (hle b List.mem_cons_self) hab
        refine List.Pairwise.cons ?_ ih
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hab'
        · exact hab'.trans (hb x hx)

/-- Two strictly ascending lists with the same members are equal. -/
theorem eq_of_pairwise_lt_of_mem_iff :
    ∀ {l₁ l₂ : List ℕ}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) →
      l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (by simp)
  | a :: t, b :: u, h₁, h₂, h => by
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | ha
      · exact e
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hb
      · exact e.symm
      have := List.rel_of_pairwise_cons h₁ hb
      have := List.rel_of_pairwise_cons h₂ ha
      omega
    subst hab
    refine congrArg _ (eq_of_pairwise_lt_of_mem_iff h₁.of_cons h₂.of_cons fun x ↦ ⟨fun hx ↦ ?_,
      fun hx ↦ ?_⟩)
    · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · have := List.rel_of_pairwise_cons h₁ hx
        omega
      · exact e
    · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · have := List.rel_of_pairwise_cons h₂ hx
        omega
      · exact e

/-! ## `distinctPositions` and `levelNodes` -/

theorem pairwise_le_mergeSort (l : List ℕ) :
    (l.mergeSort fun a b ↦ a ≤ b).Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (le := fun a b ↦ decide (a ≤ b))
    (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l).imp
    fun h ↦ by simpa using h

theorem pairwise_lt_distinctPositions (queries : List ℕ) :
    (distinctPositions queries).Pairwise (· < ·) :=
  pairwise_lt_dedupByKey_id (pairwise_le_mergeSort queries)

theorem mem_distinctPositions {queries : List ℕ} {x : ℕ} :
    x ∈ distinctPositions queries ↔ x ∈ queries := by
  simp [distinctPositions, mem_dedupByKey_id]

theorem shiftRight_mono {a b : ℕ} (h : a ≤ b) (k : ℕ) : a >>> k ≤ b >>> k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_div_right h

theorem pairwise_lt_levelNodes {positions : List ℕ} (hpos : positions.Pairwise (· ≤ ·)) (k : ℕ) :
    (levelNodes positions k).Pairwise (· < ·) :=
  pairwise_lt_dedupByKey_id (List.pairwise_map.2 (hpos.imp fun h ↦ shiftRight_mono h k))

theorem mem_levelNodes {positions : List ℕ} {k x : ℕ} :
    x ∈ levelNodes positions k ↔ ∃ p ∈ positions, p >>> k = x := by
  simp [levelNodes, mem_dedupByKey_id]

theorem levelNodes_zero {positions : List ℕ} (hpos : positions.Pairwise (· < ·)) :
    levelNodes positions 0 = positions :=
  eq_of_pairwise_lt_of_mem_iff (pairwise_lt_levelNodes (hpos.imp le_of_lt) 0) hpos
    (by simp [mem_levelNodes])

theorem xor_one_eq (n : ℕ) : n ^^^ 1 = if n % 2 = 0 then n + 1 else n - 1 := by
  split
  · exact Nat.xor_one_of_even (Nat.even_iff.2 (by assumption))
  · exact Nat.xor_one_of_odd (Nat.odd_iff.2 (by omega))

theorem shiftRight_one_eq_iff {a b : ℕ} : a >>> 1 = b >>> 1 ↔ a = b ∨ a = b ^^^ 1 := by
  rw [Nat.shiftRight_one, Nat.shiftRight_one, xor_one_eq]
  split <;> omega

/-- **The parents of a level**: the level-`k` nodes that are first children (even, or without
their sibling at the level), each shifted once, are the level-`k + 1` nodes. -/
theorem levelNodes_succ {positions : List ℕ} (hpos : positions.Pairwise (· ≤ ·)) (k : ℕ) :
    ((levelNodes positions k).filter fun n ↦ n % 2 = 0 ∨ n ^^^ 1 ∉ levelNodes positions k).map
      (· >>> 1) = levelNodes positions (k + 1) := by
  have hns := pairwise_lt_levelNodes hpos k
  refine eq_of_pairwise_lt_of_mem_iff ?_ (pairwise_lt_levelNodes hpos (k + 1)) fun x ↦ ?_
  · refine List.pairwise_map.2 ((hns.filter _).imp_of_mem fun {a b} ha hb hab ↦ ?_)
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    rcases Nat.lt_or_ge (a >>> 1) (b >>> 1) with h | h
    · exact h
    exfalso
    have h' : a >>> 1 = b >>> 1 := le_antisymm (shiftRight_mono hab.le 1) h
    rw [Nat.shiftRight_one, Nat.shiftRight_one] at h'
    have hbx : b ^^^ 1 = a := by rw [xor_one_eq]; split <;> omega
    rcases hb.2 with hb2 | hb2
    · omega
    · exact hb2 (hbx ▸ ha.1)
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, mem_levelNodes]
    constructor
    · rintro ⟨n, ⟨⟨p, hp, rfl⟩, _⟩, rfl⟩
      exact ⟨p, hp, by rw [Nat.shiftRight_add]⟩
    · rintro ⟨p, hp, rfl⟩
      by_cases hfirst : (p >>> k) % 2 = 0 ∨ (p >>> k) ^^^ 1 ∉ levelNodes positions k
      · exact ⟨p >>> k, ⟨⟨p, hp, rfl⟩, by simpa [mem_levelNodes] using hfirst⟩,
          by rw [Nat.shiftRight_add]⟩
      · simp only [not_or, not_not] at hfirst
        obtain ⟨hodd, hmem⟩ := hfirst
        refine ⟨(p >>> k) ^^^ 1, ⟨mem_levelNodes.1 hmem, Or.inl ?_⟩, ?_⟩
        · rw [xor_one_eq]; split <;> omega
        · rw [Nat.shiftRight_add, shiftRight_one_eq_iff]
          right
          rfl

/-! ## `List.lookup` on keyed lists -/

theorem lookup_of_mem_map_fst {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α}, a ∈ l.map Prod.fst → ∃ x ∈ l, x.1 = a ∧ l.lookup a = some x.2
  | [], a, h => by simp at h
  | (k, b) :: rest, a, h => by
    by_cases hak : a = k
    · subst hak
      exact ⟨(a, b), List.mem_cons_self, rfl, by simp⟩
    · have h' : a ∈ rest.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        exact h.resolve_left hak
      obtain ⟨x, hx, hx1, hlook⟩ := lookup_of_mem_map_fst h'
      refine ⟨x, List.mem_cons_of_mem _ hx, hx1, ?_⟩
      rw [List.lookup_cons, beq_eq_false_iff_ne.2 hak]
      exact hlook

theorem lookup_eq_none_of_not_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α}
    (h : a ∉ l.map Prod.fst) : l.lookup a = none := by
  rw [List.lookup_eq_none_iff]
  intro p hp
  rw [bne_iff_ne]
  exact fun e ↦ h (List.mem_map.2 ⟨p, hp, e.symm⟩)

theorem lookup_map_key {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) :
    ∀ {l : List α} {a : α}, a ∈ l → (l.map fun n ↦ (n, f n)).lookup a = some (f a)
  | [], a, h => by simp at h
  | k :: rest, a, h => by
    rw [List.map_cons, List.lookup_cons]
    by_cases hak : a = k
    · subst hak
      simp
    · have h' : a ∈ rest := (List.mem_cons.1 h).resolve_left hak
      rw [beq_eq_false_iff_ne.2 hak]
      exact lookup_map_key f h'

end

end LeanVM.Wire
