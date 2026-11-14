/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E07

  The analysis accepts the guest's functions 600 to 849, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `600` to `849`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE07 : (List.range' 600 250).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
