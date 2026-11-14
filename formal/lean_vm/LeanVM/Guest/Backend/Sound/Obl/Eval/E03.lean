/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E03

  The analysis accepts the guest's functions 36 to 36, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `36` to `36`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE03 : (List.range' 36 1).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
