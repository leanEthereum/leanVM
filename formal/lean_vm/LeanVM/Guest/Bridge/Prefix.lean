/-
  LeanVM.Guest.Bridge.Prefix

  A path through leading atoms: its walk and its calls.
-/

module

public import LeanVM.Guest.Bridge.Defs
public import LeanVM.Guest.Pops

/-!
# A path through leading atoms

`walk_atoms`: a block's walk past leading atoms is the rest's, prefixed with their events; `calls_atoms`: those events call nothing.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

public section

theorem walk_atoms (σ : Val) : ∀ (as : List Atom) (ss : List Stmt),
    walk σ (as.map Stmt.atom ++ ss) = (walk σ ss).pre (as.map Ev.atom)
  | [], ss => by cases h : walk σ ss <;> simp [Out.pre, h]
  | a :: as, ss => by
    rw [List.map_cons, List.cons_append, walk, walk1, walk_atoms σ as ss, Out.seq]
    cases walk σ ss <;> simp [Out.pre]

theorem calls_atoms : ∀ as : List Atom, calls (as.map Ev.atom) = []
  | [] => rfl
  | _ :: as => by simp only [List.map_cons, calls, List.filterMap_cons, Ev.call?]; exact calls_atoms as

end

end LeanVM.Guest.Bridge
