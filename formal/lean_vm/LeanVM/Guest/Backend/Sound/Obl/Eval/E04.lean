/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E04

  The analysis accepts the guest's functions 37 to 334, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `37` to `334`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE04 : (List.range' 37 298).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
