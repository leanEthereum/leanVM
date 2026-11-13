/-
  LeanVM.Guest.B1.Digest.ChildListCW1

  `child_claim_list_any`'s big frame loop `child_claim_list_any_loop0`, its records evaluated by windows of nine
  (windows 4–7), each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem anycWin_4 : anycWin 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_5 : anycWin 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_6 : anycWin 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_7 : anycWin 7 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
