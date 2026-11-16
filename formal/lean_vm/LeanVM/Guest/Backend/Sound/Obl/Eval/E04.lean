/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E04

  The analysis accepts the guest's functions 754 to 959, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `754` to `795`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_754 : (List.range' 754 42).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `796` to `840`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_796 : (List.range' 796 45).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `841` to `885`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_841 : (List.range' 841 45).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `886` to `929`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_886 : (List.range' 886 44).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `930` to `959`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_930 : (List.range' 930 30).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
