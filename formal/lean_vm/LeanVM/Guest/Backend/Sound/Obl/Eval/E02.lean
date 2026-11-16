/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E02

  The analysis accepts the guest's functions 288 to 481, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `288` to `312`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_288 : (List.range' 288 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `313` to `348`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_313 : (List.range' 313 36).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `349` to `373`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_349 : (List.range' 349 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `374` to `398`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_374 : (List.range' 374 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `399` to `423`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_399 : (List.range' 399 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `424` to `448`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_424 : (List.range' 424 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `449` to `481`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_449 : (List.range' 449 33).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
