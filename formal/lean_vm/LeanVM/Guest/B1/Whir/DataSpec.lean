/-
  LeanVM.Guest.B1.Whir.DataSpec

  What the kernel checks of each size's core IR: `open_stacked__L{m}` is the template at the
  size's configuration.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpecP
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Common.Find

/-!
# The sizes' core IR, as the templates

`FnIs` and `OsData m` are `Whir/DataSpecP.lean`'s statements for the guest's `coreProgram`;
`Whir/DataAll.lean` and `Whir/HelperAll.lean` give them from the per-function data, each function
found by its position (`coreProgram_find?_at`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The core IR holds the function `name` with the parameters `ps` and the body `body`. -/
abbrev FnIs (name : String) (ps : List V) (body : List Stmt) : Prop := FnIsP coreProgram name ps body

/-- **Size `m`'s core IR is its template.** -/
def OsData (m : Nat) : Prop :=
  FnIs ("open_stacked__L" ++ natStr m) (osParams 11) (osBody (osCfg m))

end
end LeanVM.Guest.B1.Whir
