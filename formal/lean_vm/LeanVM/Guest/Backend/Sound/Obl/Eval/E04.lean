/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E04

  The analysis accepts the guest's functions 764 to 1018, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `764` to `805`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_764 : (List.range' 764 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `806` to `850`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_806 : (List.range' 806 45).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `851` to `895`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_851 : (List.range' 851 45).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `896` to `939`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_896 : (List.range' 896 44).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `940` to `964`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_940 : (List.range' 940 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `965` to `989`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_965 : (List.range' 965 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `990` to `1018`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_990 : (List.range' 990 29).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
