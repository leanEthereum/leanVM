/-
  LeanVM.Guest.B1.Main.NoHeapPops

  No call tree of the guest pops a `heap_sizes` entry: no witness hint of the program is on that stream (the executor's `allocAdvice` pops it).
-/

module

public import LeanVM.Guest.B1.Main.NoHeapCheck

/-!
# No `heap_sizes` entry in the pops

From `coreProgram_noHeap` (`NoHeapCheck`): `splice_mem`: a spliced entry is an atom's or a callee's. `pops_noHeap`: every valid tree's entries are on other streams.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem atom_pops_noHeap {rd : Reader} {σ : Val} {a : Atom} (ha : atomNoHeap a = true) :
    ∀ p ∈ a.pops rd σ, p.1 ≠ Hints.heapSizeStream := by
  intro p hp
  cases a with
  | hint x =>
    cases x with
    | witness s d =>
      simp only [Atom.pops, Hint.pops, List.mem_singleton] at hp
      subst hp
      simpa [atomNoHeap] using ha
    | _ => simp [Atom.pops, Hint.pops] at hp
  | _ => simp [Atom.pops] at hp

/-- **A spliced entry is an atom's or a callee's.** -/
theorem splice_mem {rd : Reader} {σ : Val} : ∀ (es : List Ev) (ks : List (List Pop)) {p : Pop},
    p ∈ splice rd σ es ks → (∃ a, Ev.atom a ∈ es ∧ p ∈ a.pops rd σ) ∨ ∃ k ∈ ks, p ∈ k
  | [], _, _, h => by simp [splice] at h
  | .atom a :: es, ks, p, h => by
      rw [splice, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl ⟨a, List.mem_cons_self, h⟩
      · rcases splice_mem es ks h with ⟨b, hb, hp⟩ | h
        · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, hp⟩
        · exact Or.inr h
  | .inK _ :: es, ks, p, h => by
      rw [splice] at h
      rcases splice_mem es ks h with ⟨b, hb, hp⟩ | h
      · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, hp⟩
      · exact Or.inr h
  | .call .. :: es, ks, p, h | .skip .. :: es, ks, p, h => by
      rw [splice, List.mem_append] at h
      rcases h with h | h
      · cases ks with
        | nil => simp at h
        | cons k ks => exact Or.inr ⟨k, List.mem_cons_self, h⟩
      · rcases splice_mem es ks.tail h with ⟨b, hb, hp⟩ | ⟨k, hk, hp⟩
        · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, hp⟩
        · exact Or.inr ⟨k, List.mem_of_mem_tail hk, hp⟩

variable {rd : Reader}

mutual
/-- **A valid tree pops no `heap_sizes` entry.** -/
theorem pops_noHeap : ∀ (t : Tree) {args rets : List E}, t.Valid coreProgram rd args rets →
    ∀ p ∈ t.pops coreProgram rd, p.1 ≠ Hints.heapSizeStream
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, p, hp => by
      rw [Tree.pops_node hf hw] at hp
      rcases splice_mem es _ hp with ⟨a, ha, hpa⟩ | ⟨k, hk', hpk⟩
      · have hmem : a ∈ B2C.lAtoms fn.body := B2C.walk_atoms (σ := σ) fn.body (by rw [hw]; exact ha)
        have hall := List.all_eq_true.mp coreProgram_noHeap fn (List.mem_of_find?_eq_some hf)
        exact atom_pops_noHeap (List.all_eq_true.mp hall a hmem) p hpa
      · exact popsKids_noHeap kids σ (calls es) hk k hk' p hpk
  | .phantom .., _, _, h, _, _ => h.elim

/-- `pops_noHeap` for the callees. -/
theorem popsKids_noHeap : ∀ (ks : List Tree) (σ : Val) (cs : List Call), Tree.KidsValid coreProgram rd σ cs ks →
    ∀ k ∈ Tree.popsKids coreProgram rd ks, ∀ p ∈ k, p.1 ≠ Hints.heapSizeStream
  | [], _, _, _ => by rw [Tree.popsKids]; exact fun _ h => (List.not_mem_nil h).elim
  | k :: ks, σ, c :: cs, ⟨_, hc, hks⟩ => by
      rw [Tree.popsKids]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact pops_noHeap k hc
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          intro p hp
          rw [Tree.pops] at hp
          exact (List.not_mem_nil hp).elim
      · exact popsKids_noHeap ks σ cs hks x hx
  | _ :: _, _, [], h => h.elim
end

end
end LeanVM.Guest.B1.Main
