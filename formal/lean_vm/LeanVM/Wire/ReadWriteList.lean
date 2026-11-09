/-
  LeanVM.Wire.ReadWriteList

  List facts of the wire encoding for a key of any order: `dedupByKey` on a list sorted by its key
  keeps the first of each key, strictly ascending; and what `carriedSiblings` keeps.
-/

module

public import LeanVM.Wire.Encoding

/-!
# `dedupByKey` by any key, and `carriedSiblings`

`Prover.phaseToBytes` deduplicates paths by their position and nodes by their index
(`dedupByKey Opening.leafIndex`, `dedupByKey Prod.fst`) after sorting them by that key. On a list
sorted by its key, `dedupByKey` gives the members strictly ascending by key
(`pairwise_key_lt_dedupByKey`), and a member is kept exactly when it is the first of its key
(`mem_dedupByKey_iff_find?`). `carriedSiblings` keeps the nodes whose sibling is not a node, in
order (`mem_carriedSiblings`, `carriedSiblings_sublist`).

The facts for `dedupByKey id`, `distinctPositions` and `levelNodes` are in
`LeanVM.Wire.UnpruneList`.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Protocol.Compile

public section

/-! ## `dedupByKey` -/

/-- A list's deduplication starts with the list's first member. -/
theorem head?_dedupByKey {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ l : List α, (dedupByKey key l).head? = l.head?
  | [] => rfl
  | a :: rest => by
    rw [dedupByKey]
    split
    · rfl
    · split <;> rfl

/-- **On a list sorted by its key, `dedupByKey` is strictly ascending by key.** -/
theorem pairwise_key_lt_dedupByKey {α β : Type} [LinearOrder β] (key : α → β) :
    ∀ {l : List α}, l.Pairwise (fun a b ↦ key a ≤ key b) →
      (dedupByKey key l).Pairwise (fun a b ↦ key a < key b)
  | [], _ => by simp [dedupByKey]
  | a :: rest, hl => by
    have ih := pairwise_key_lt_dedupByKey key hl.of_cons
    rw [dedupByKey]
    split
    · simp
    · rename_i b kept heq
      rw [heq] at ih
      have hb : ∀ x ∈ kept, key b < key x := fun x hx ↦ List.rel_of_pairwise_cons ih hx
      have hhead := head?_dedupByKey key rest
      rw [heq] at hhead
      obtain ⟨rest', hrest⟩ : ∃ rest', rest = b :: rest' := by
        cases rest with
        | nil => simp at hhead
        | cons c rest' =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          exact ⟨rest', by rw [hhead]⟩
      have hab : key a ≤ key b := List.rel_of_pairwise_cons hl (by rw [hrest]; simp)
      split
      · rename_i hkey
        refine List.Pairwise.cons (fun x hx ↦ ?_) ih.of_cons
        rw [hkey]
        exact hb x hx
      · rename_i hkey
        have hab' : key a < key b := lt_of_le_of_ne hab hkey
        refine List.Pairwise.cons (fun x hx ↦ ?_) ih
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hab'
        · exact hab'.trans (hb x hx)

/-- A member that is the first of its key is kept, whatever the order. -/
theorem mem_dedupByKey_of_find? {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ {l : List α} {x : α}, l.find? (fun y ↦ key y = key x) = some x → x ∈ dedupByKey key l
  | [], x, h => by simp at h
  | a :: rest, x, h => by
    rw [List.find?_cons] at h
    by_cases hax : key a = key x
    · simp only [hax, decide_true, Option.some.injEq] at h
      subst h
      rw [dedupByKey]
      split
      · exact List.mem_singleton_self _
      · split <;> exact List.mem_cons_self
    · simp only [hax, decide_false] at h
      have ih := mem_dedupByKey_of_find? key h
      rw [dedupByKey]
      split
      · rename_i heq
        rw [heq] at ih
        simp at ih
      · rename_i b kept heq
        rw [heq] at ih
        split
        · rename_i hab
          rcases List.mem_cons.1 ih with rfl | hx
          · exact absurd hab hax
          · exact List.mem_cons_of_mem _ hx
        · exact List.mem_cons_of_mem _ ih

/-- **On a list sorted by its key, `dedupByKey` keeps the first of each key.** -/
theorem find?_of_mem_dedupByKey {α β : Type} [LinearOrder β] (key : α → β) :
    ∀ {l : List α}, l.Pairwise (fun a b ↦ key a ≤ key b) → ∀ {x : α}, x ∈ dedupByKey key l →
      l.find? (fun y ↦ key y = key x) = some x
  | [], _, x, hx => by simp [dedupByKey] at hx
  | a :: rest, hl, x, hx => by
    have hsorted := pairwise_key_lt_dedupByKey key hl.of_cons
    rw [dedupByKey] at hx
    rw [List.find?_cons]
    split at hx
    · rw [List.mem_singleton] at hx
      subst hx
      simp
    · rename_i b kept heq
      rw [heq] at hsorted
      have hhead := head?_dedupByKey key rest
      rw [heq] at hhead
      have hab : key a ≤ key b := List.rel_of_pairwise_cons hl (List.mem_of_head? hhead.symm)
      -- a member past the head of the rest's deduplication has a key above `a`'s
      have hpast : ∀ y ∈ kept, key a < key y := fun y hy ↦
        lt_of_le_of_lt hab (List.rel_of_pairwise_cons hsorted hy)
      have hrest : ∀ y ∈ b :: kept, rest.find? (fun z ↦ key z = key y) = some y := fun y hy ↦
        find?_of_mem_dedupByKey key hl.of_cons (heq ▸ hy)
      split at hx
      · rename_i hkey
        rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · simp only [(hpast x hx).ne, decide_false]
          exact hrest x (List.mem_cons_of_mem _ hx)
      · rename_i hkey
        rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · rcases List.mem_cons.1 hx with rfl | hx
          · simp only [hkey, decide_false]
            exact hrest x List.mem_cons_self
          · simp only [(hpast x hx).ne, decide_false]
            exact hrest x (List.mem_cons_of_mem _ hx)

/-- **What `dedupByKey` keeps, on a list sorted by its key:** the first member of each key. -/
theorem mem_dedupByKey_iff_find? {α β : Type} [LinearOrder β] (key : α → β) {l : List α}
    (hl : l.Pairwise (fun a b ↦ key a ≤ key b)) {x : α} :
    x ∈ dedupByKey key l ↔ l.find? (fun y ↦ key y = key x) = some x :=
  ⟨find?_of_mem_dedupByKey key hl, mem_dedupByKey_of_find? key⟩

/-! ## `carriedSiblings` -/

/-- **The nodes whose sibling a phase carries:** the nodes whose sibling is not a node. -/
theorem mem_carriedSiblings {nodes : List ℕ} {node : ℕ} :
    node ∈ carriedSiblings nodes ↔ node ∈ nodes ∧ node ^^^ 1 ∉ nodes := by
  simp [carriedSiblings]

/-- The carried nodes are in the nodes' order. -/
theorem carriedSiblings_sublist (nodes : List ℕ) : (carriedSiblings nodes).Sublist nodes :=
  List.filter_sublist

/-- The carried nodes of strictly ascending nodes are strictly ascending. -/
theorem pairwise_carriedSiblings {R : ℕ → ℕ → Prop} {nodes : List ℕ} (h : nodes.Pairwise R) :
    (carriedSiblings nodes).Pairwise R :=
  h.sublist (carriedSiblings_sublist nodes)

end

end LeanVM.Wire
