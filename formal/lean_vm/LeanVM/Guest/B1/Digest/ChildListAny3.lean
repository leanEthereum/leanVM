/-
  LeanVM.Guest.B1.Digest.ChildListAny3

  Windows 12–15 of `child_claim_list_any`'s big frame loop `child_claim_list_any_loop0`: blocks
  48–63, records 108–135, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem anyWin_12 : anyWin 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_13 : anyWin 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_14 : anyWin 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_15 : anyWin 15 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
