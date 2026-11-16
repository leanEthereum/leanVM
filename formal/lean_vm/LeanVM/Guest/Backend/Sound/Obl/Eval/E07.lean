/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E07

  The analysis accepts the guest's functions 1376 to 1548, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1376` to `1400`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1376 : (List.range' 1376 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1401` to `1431`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1401 : (List.range' 1401 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1432` to `1504`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1432 : (List.range' 1432 73).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1505` to `1548`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1505 : (List.range' 1505 44).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
