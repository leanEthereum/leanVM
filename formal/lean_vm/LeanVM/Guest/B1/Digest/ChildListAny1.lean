/-
  LeanVM.Guest.B1.Digest.ChildListAny1

  Windows 4–7 of `child_claim_list_any`'s big frame loop `child_claim_list_any_loop0`: blocks
  16–31, records 36–71, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem anyWin_4 : anyWin 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_5 : anyWin 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_6 : anyWin 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyWin_7 : anyWin 7 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
