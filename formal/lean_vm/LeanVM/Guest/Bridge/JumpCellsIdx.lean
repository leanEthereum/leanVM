/-
  LeanVM.Guest.Bridge.JumpCellsIdx

  The jump cells' data check of a compiled function, by index.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Defs

/-!
# The jump cells' check by index

`jcData j`: `jcDataD` on compiled function `j`'s plumbing, frame size, certificate, hint-only cells (`extraOf`), core IR, code and whether it is `main`; `Bridge/JumpCells/All.lean` proves it of every function from the checks of each function's own data.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.B2C

@[expose] public section

/-- The jump cells' facts of function `j`'s data. -/
noncomputable def jcData (j : ℕ) : Bool :=
  jcDataD (plumbOf j) (fsN j) (certOf j) (extraOf j) (coreOf j) (fnOf j).code (j == 1)

end

end LeanVM.Guest.Bridge
