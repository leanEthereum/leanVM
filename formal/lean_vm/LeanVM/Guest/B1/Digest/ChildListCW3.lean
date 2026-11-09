/-
  LeanVM.Guest.B1.Digest.ChildListCW3

  `child_claim_list_any`'s big frame loop `__loop17`, its records evaluated by windows of nine
  (windows 12–15), each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem anycWin_12 : anycWin 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_13 : anycWin 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_14 : anycWin 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_15 : anycWin 15 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
