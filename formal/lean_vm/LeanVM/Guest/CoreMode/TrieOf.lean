/-
  LeanVM.Guest.CoreMode.TrieOf

  A set of keys as a trie of units, from the list of its keys: how generated data writes the frame
  walk's cut states' heap sets (`FSt.hq`, `hs`).
-/

module

public import LeanVM.Guest.ExecCore

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Exec

@[expose] public section

/-- **The keys `ks` as a set**: each stored, within 64 levels (every key below `2^63`). -/
noncomputable def unitOf (ks : List ℕ) : Trie Unit :=
  ks.foldl (fun t k ↦ t.set () 64 k) .nil

end

end LeanVM.Guest.CoreMode
