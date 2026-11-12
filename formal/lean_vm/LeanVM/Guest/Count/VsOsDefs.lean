/-
  LeanVM.Guest.Count.VsOsDefs

  `open_stacked`'s words at an arm by the search tree's lookups (`osCF`), which the kernel
  evaluates one module per arm (`Count/VsOs*`). Few imports, so that each module stays small.
-/

module

public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.Place.OsSpec

namespace LeanVM.Guest.Count

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

/-- `open_stacked`'s words at the arm `m`, its name spelled by `natStr`, by the search tree's
lookups. -/
noncomputable def osCF (m : ℕ) : ℕ :=
  B1.osBos fsFast wSBFast ("open_stacked__L" ++ natStr m) (osCfg m)

end
end LeanVM.Guest.Count
