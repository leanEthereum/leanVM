/-
  LeanVM.Guest.B1.Digest.ChildListAny2

  Windows 8–11 of `child_claim_list_any`'s big frame loop `__loop17`: blocks
  32–47, records 72–107, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem anyWin_8 : anyWin 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_9 : anyWin 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_10 : anyWin 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_11 : anyWin 11 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
