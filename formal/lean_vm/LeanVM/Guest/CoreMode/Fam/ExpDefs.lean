/-
  LeanVM.Guest.CoreMode.Fam.ExpDefs

  The exponent of a constant word `g^z` (`powOf1`).
-/

module

public import LeanVM.Guest.CoreMode.Fam.FamDefs

/-!
# A constant word's exponent

`powOf1 c`: `0` for `1`, else `powOf c`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The exponent of a word `g^z`: `1`'s, or one the guest's powers name (`powOf`). -/
noncomputable def powOf1 (c : E) : Option ℕ := if c.limb 1 = 0 ∧ c.limb 0 = 1 then some 0 else powOf c

end

end LeanVM.Guest.Res
