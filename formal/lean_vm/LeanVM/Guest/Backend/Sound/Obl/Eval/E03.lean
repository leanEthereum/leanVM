/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E03

  The analysis accepts the guest's functions 472 to 753, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `472` to `504`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_472 : (List.range' 472 33).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `505` to `545`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_505 : (List.range' 505 41).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `546` to `586`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_546 : (List.range' 546 41).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `587` to `627`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_587 : (List.range' 587 41).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `628` to `669`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_628 : (List.range' 628 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `670` to `711`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_670 : (List.range' 670 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `712` to `753`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_712 : (List.range' 712 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
