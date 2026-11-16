/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E06

  The analysis accepts the guest's functions 1230 to 1434, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1230` to `1260`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1230 : (List.range' 1230 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1261` to `1288`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1261 : (List.range' 1261 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1289` to `1316`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1289 : (List.range' 1289 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1317` to `1347`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1317 : (List.range' 1317 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1348` to `1375`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1348 : (List.range' 1348 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1376` to `1403`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1376 : (List.range' 1376 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1404` to `1434`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1404 : (List.range' 1404 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
