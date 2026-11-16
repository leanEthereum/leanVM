/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E06

  The analysis accepts the guest's functions 1171 to 1375, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `1171` to `1201`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1171 : (List.range' 1171 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1202` to `1229`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1202 : (List.range' 1202 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1230` to `1257`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1230 : (List.range' 1230 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1258` to `1288`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1258 : (List.range' 1258 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1289` to `1316`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1289 : (List.range' 1289 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1317` to `1344`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1317 : (List.range' 1317 28).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `1345` to `1375`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_1345 : (List.range' 1345 31).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
