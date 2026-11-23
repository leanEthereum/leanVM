module

public import LeanVM.Guest.Mode.Abs

/-!
# Signatures by key

`sigTrie l`: the signatures `l`, each at its own entry `G.pc`, as a frame walk and a frame interface look a
callee up. Generated data names a function's callees by key (`[Fn.«a».csig, Fn.«b».csig]`), not as a trie
keyed by their pcs.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- The levels of a trie of signatures by entry pc. -/
def sigDepth : ℕ := 32

/-- **The signatures `l` by entry pc**, each at its own `pc`. -/
noncomputable def sigTrie (l : List Mode.Sig) : Trie Mode.Sig :=
  l.foldl (fun t G ↦ t.set G sigDepth G.pc) .nil

end

end LeanVM.Guest.CoreMode
