module

public import LeanVM.Guest.Mode.SoundJoin
/-!
# What a frame's return gives

`RetHolds`: a function's guarantees at its return. `entry_w`: a key of a trie built from a list is in the
list or the trie.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- What a function guarantees at a return, over its frame. -/
def RetHolds (s : St) (G : Sig) : Prop :=
  (∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) ∧ (∀ m ∈ G.post, HW s m) ∧
    (∀ r ∈ G.postR, RW s r) ∧ (∀ q ∈ G.postP, PW s q.1 q.2) ∧
    (∀ p ∈ G.retV, ∃ u, s.mem.get (s.fp + p.1) = some u ∧ MonoVal s p.2 u) ∧
    (∀ p ∈ G.postT, LTF s p.1 p.2) ∧ ∀ q ∈ G.postC, CndHolds s ⟨q.1, q.2.1, [], [], [], q.2.2, []⟩

/-! ## A cell the walk knows written has a word -/

/-! ## Entry -/

theorem entry_w {l : List ℕ} : ∀ {t : Exec.Trie Unit} {o : ℕ},
    (l.foldl (fun t o ↦ t.set () Exec.envDepth o) t).get o = some () → o ∈ l ∨ t.get o = some () := by
  induction l with
  | nil => intro t o h; exact Or.inr h
  | cons a l ih =>
    intro t o h
    rcases ih h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases Exec.Trie.get_set h with ⟨rfl, -⟩ | h
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h

/-! ## Calls and returns -/

end

end LeanVM.Guest.Mode
