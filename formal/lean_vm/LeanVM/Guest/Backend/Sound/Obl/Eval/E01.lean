/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.E01

  The analysis accepts the guest's functions 113 to 287, by kernel evaluation.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **The analysis accepts functions `113` to `137`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_113 : (List.range' 113 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `138` to `162`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_138 : (List.range' 138 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `163` to `187`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_163 : (List.range' 163 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `188` to `212`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_188 : (List.range' 188 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `213` to `237`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_213 : (List.range' 213 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `238` to `262`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_238 : (List.range' 238 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

/-- **The analysis accepts functions `263` to `287`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_263 : (List.range' 263 25).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
