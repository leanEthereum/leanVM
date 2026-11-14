/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E10

  The analysis accepts the guest's functions 1350 to 1600, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1350` to `1600`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE10 : (List.range' 1350 251).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
