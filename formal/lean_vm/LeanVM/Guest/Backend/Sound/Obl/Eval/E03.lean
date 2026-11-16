/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E03

  The analysis accepts the guest's functions 482 to 763, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `482` to `514`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_482 : (List.range' 482 33).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `515` to `555`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_515 : (List.range' 515 41).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `556` to `596`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_556 : (List.range' 556 41).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `597` to `637`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_597 : (List.range' 597 41).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `638` to `679`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_638 : (List.range' 638 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `680` to `721`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_680 : (List.range' 680 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `722` to `763`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_722 : (List.range' 722 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
