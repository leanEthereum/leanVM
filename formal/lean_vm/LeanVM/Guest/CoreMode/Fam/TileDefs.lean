/-
  LeanVM.Guest.CoreMode.Fam.TileDefs

  The tile families of the `sub` residuals: a run cut into parts whose exponents add up to its
  bound, a run one point past another, offsets modulo `g`'s order, and a run past a lift's shift.
-/

module

public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# Offsets modulo the order, and indices that are powers

`ordG`: `g`'s order `2^64 - 1`. `idxPow j w`: an index whose base is a power of `g`, a selector's bound
(`ltSelB`) or named by a witness.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-- The order of `g`. -/
abbrev ordG : ℕ := 2 ^ 64 - 1

/-! ## Offsets modulo the order -/

/-- An index whose exponent's base is a selector's of function `j` (`ltSelB`) or a cell `pw` bounds,
so a power of `g`. -/
noncomputable def idxPow (j : ℕ) (w : Wit) : Mode.Idx → Bool
  | .num _ => true
  | .ex B _ => ltSelB j (.lt (.ex B 0) (.num (2 ^ 62))) || match B with
    | .fr o => pw j w o
    | _ => false

end

end LeanVM.Guest.Res
