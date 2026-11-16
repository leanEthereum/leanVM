/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E05

  The analysis accepts the guest's functions 960 to 1170, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `960` to `993`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_960 : (List.range' 960 34).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `994` to `1025`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_994 : (List.range' 994 32).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1026` to `1050`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1026 : (List.range' 1026 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1051` to `1082`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1051 : (List.range' 1051 32).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1083` to `1114`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1083 : (List.range' 1083 32).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1115` to `1145`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1115 : (List.range' 1115 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1146` to `1170`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1146 : (List.range' 1146 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
