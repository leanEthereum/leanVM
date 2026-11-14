/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E00

  The analysis accepts the guest's functions 0 to 112, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `0` to `10`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_0 : (List.range' 0 11).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `11` to `11`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_11 : (List.range' 11 1).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `12` to `35`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_12 : (List.range' 12 24).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `36` to `36`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_36 : (List.range' 36 1).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `37` to `61`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_37 : (List.range' 37 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `62` to `86`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_62 : (List.range' 62 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `87` to `112`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_87 : (List.range' 87 26).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
