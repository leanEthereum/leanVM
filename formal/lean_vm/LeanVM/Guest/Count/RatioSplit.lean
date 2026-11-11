/-
  LeanVM.Guest.Count.RatioSplit

  A ratio subtree's closure check of one large function, in pieces of its body: each piece's
  callees by index, checked on its own, the pieces appended.
-/

module

public import LeanVM.Guest.Count.RatioBase

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

/-- Function `i`'s body. -/
noncomputable def krBody (i : ℕ) : List Stmt := ((coreProgram[i]?).getD default).body

/-- **The statements `[a, a + n)` of function `i`'s body call the functions of indices `L`**, all
in `J`. -/
noncomputable def krPiece (J : List ℕ) (i a n : ℕ) (L : List ℕ) : Bool :=
  (Stmt.blockCallees (((krBody i).drop a).take n) == L.map krName) &&
    L.all fun k => decide (k ∈ J) && Nat.blt k 1752

end
end LeanVM.Guest.Count
