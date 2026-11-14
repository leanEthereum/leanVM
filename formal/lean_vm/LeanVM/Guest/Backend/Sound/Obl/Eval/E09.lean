/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E09

  The analysis accepts the guest's functions 1100 to 1349, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1100` to `1349`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE09 : (List.range' 1100 250).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
