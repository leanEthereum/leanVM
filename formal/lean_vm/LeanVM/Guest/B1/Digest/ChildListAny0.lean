/-
  LeanVM.Guest.B1.Digest.ChildListAny0

  Windows 0–3 of `child_claim_list_any`'s big frame loop `__loop17`: blocks
  0–15, records 0–35, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem anyWin_0 : anyWin 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_1 : anyWin 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_2 : anyWin 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_3 : anyWin 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
