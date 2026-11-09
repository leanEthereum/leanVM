/-
  LeanVM.Guest.B1.Common.Atoms

  A block of atoms holds exactly when each of its atoms does.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# Blocks of atoms

A template with no control flow (`AllAtoms`) holds exactly when every atom in it holds
(`holdsList_atoms`): its facts are read off by membership, and its honest valuation is checked
atom by atom.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Every statement of the block is an atom. -/
def AllAtoms (ss : List Stmt) : Prop := ∀ s ∈ ss, ∃ a, s = .atom a

theorem allAtoms_nil : AllAtoms [] := fun _ h => absurd h (by simp)

theorem allAtoms_append {ss ts : List Stmt} (h1 : AllAtoms ss) (h2 : AllAtoms ts) :
    AllAtoms (ss ++ ts) := fun s hs => by
  rcases List.mem_append.mp hs with h | h
  · exact h1 s h
  · exact h2 s h

theorem allAtoms_flatten {bs : List (List Stmt)} (h : ∀ b ∈ bs, AllAtoms b) :
    AllAtoms bs.flatten := fun s hs => by
  obtain ⟨b, hb, hs⟩ := List.mem_flatten.mp hs
  exact h b hb s hs

theorem allAtoms_map_flatten {α : Type} {l : List α} {f : α → List Stmt}
    (h : ∀ x ∈ l, AllAtoms (f x)) : AllAtoms (l.map f).flatten :=
  allAtoms_flatten fun b hb => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact h x hx

theorem allAtoms_cons {a : Atom} {ss : List Stmt} (h : AllAtoms ss) : AllAtoms (.atom a :: ss) :=
  fun s hs => by
    rcases List.mem_cons.mp hs with rfl | h'
    · exact ⟨a, rfl⟩
    · exact h s h'

/-- **A block of atoms holds exactly when every atom of it does.** -/
theorem holdsList_atoms : ∀ {ss : List Stmt}, AllAtoms ss → ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsList C rd σ ss next kret ↔ (∀ a, Stmt.atom a ∈ ss → a.Holds rd σ) ∧ next)
  | [], _, _, _ => by simp [Stmt.HoldsList]
  | s :: ss, h, next, kret => by
    obtain ⟨a, rfl⟩ := h s (by simp)
    have ih := holdsList_atoms (ss := ss) (fun t ht => h t (by simp [ht])) next kret
    simp only [Stmt.HoldsList, Stmt.Holds, ih, List.mem_cons, Stmt.atom.injEq]
    constructor
    · rintro ⟨ha, hall, hn⟩
      exact ⟨fun b hb => by rcases hb with rfl | hb; exacts [ha, hall b hb], hn⟩
    · rintro ⟨hall, hn⟩
      exact ⟨hall a (Or.inl rfl), fun b hb => hall b (Or.inr hb), hn⟩

end
end LeanVM.Guest.B1
