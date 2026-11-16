/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E05

  The analysis accepts the guest's functions 1019 to 1229, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1019` to `1052`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1019 : (List.range' 1019 34).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1053` to `1084`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1053 : (List.range' 1053 32).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1085` to `1109`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1085 : (List.range' 1085 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1110` to `1141`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1110 : (List.range' 1110 32).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1142` to `1173`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1142 : (List.range' 1142 32).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1174` to `1204`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1174 : (List.range' 1174 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1205` to `1229`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1205 : (List.range' 1205 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
