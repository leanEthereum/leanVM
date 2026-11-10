/-
  LeanVM.Guest.B1.VerifySub.Stream

  The stream before the opening, as the decoder reads it: the words up to the cursor.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# The stream before the opening

`readsAt_cursor`: the words a run read at `p`, the cursor having moved to `p·g^n` past them, are
`wordsAt p (cursorLen p q)`: the memory bounds their count by `2^κ ≤ 2^32` (`mem_size_le`), so
`cursorLen` finds it. `readsAt_append` (KeccakGkr's) puts consecutive runs together.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The words up to the cursor**: a run of words read at `p`, the cursor `q = p·g^n` past
them. -/
theorem readsAt_cursor {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p q : E} {xs : List E}
    (hr : ReadsAt L.read p xs) (hq : q = p * gen ^ xs.length) (hne : xs ≠ []) :
    wordsAt L.read p (cursorLen p q) = xs := by
  have hp : p ≠ 0 := by
    obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ne_zero_of_load (by omega) L (hr 0 (by simp))
  rw [cursorLen_eq hp hq (mem_size_le hκ L hr), wordsAt_eq hr]

end
end LeanVM.Guest.B1.VerifySub
