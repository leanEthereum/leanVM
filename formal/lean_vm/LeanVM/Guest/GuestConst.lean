/-
  LeanVM.Guest.GuestConst

  `guest_const% C`: the value of the guest's global constant `C`, as a literal.
-/

module

public meta import Lean.Elab.Term

/-!
# The guest's constants

`guest-export` writes each top-level constant `C` of the guest to `Data/Source.lean` as
`Data.const_C`, a literal. `guest_const% C` elaborates to that literal, so a definition that mirrors
`C` (`abbrev resBatch : ℕ := guest_const% RES_BATCH`) reads exactly as a hand copy of it, and a
change to `C` in the guest reaches it by the export alone.
-/

public meta section

namespace LeanVM.Guest.GuestConst

open Lean Elab Term

/-- `guest_const% C`: the value of the guest's global constant `C`. -/
elab:max "guest_const% " c:ident : term => do
  let n := `LeanVM.Guest.Data ++ Name.mkSimple ("const_" ++ c.getId.toString)
  let some (.defnInfo d) := (← getEnv).find? n | throwErrorAt c "no guest constant {c.getId} ({n})"
  return d.value

end LeanVM.Guest.GuestConst
