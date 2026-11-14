/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E01

  The analysis accepts the guest's functions 11 to 11, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `11` to `11`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE01 : (List.range' 11 1).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
