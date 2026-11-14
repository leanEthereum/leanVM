/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E07

  The analysis accepts the guest's functions 1435 to 1600, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1435` to `1459`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1435 : (List.range' 1435 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1460` to `1490`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1460 : (List.range' 1460 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1491` to `1556`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1491 : (List.range' 1491 66).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1557` to `1600`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1557 : (List.range' 1557 44).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
