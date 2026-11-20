/-
  LeanVM.Guest.CoreMode.Fn.column_selector.Data

  `column_selector`'s own routing data (`CoreMode/FnReg.lean`): its specializations' caller, whose facts are carried to them.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.B1.Selectors.InterfaceP

namespace LeanVM.Guest.CoreMode.Own.column_selector

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its specializations' caller**: each `column_selector__L{κ}` called by `check_opening_terminal` (`Res.callersG`). -/
def stCallers : List (String × String) :=
  (List.range 31).map fun κ ↦ (B1.Tables.lName "column_selector" κ, name% «check_opening_terminal»)

end

end LeanVM.Guest.CoreMode.Own.column_selector
