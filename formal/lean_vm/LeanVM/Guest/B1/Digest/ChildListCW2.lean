/-
  LeanVM.Guest.B1.Digest.ChildListCW2

  `child_claim_list_any`'s big frame loop `child_claim_list_any_loop0`, its records evaluated by
  windows of nine (windows 8–11), each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem anycWin_8 : anycWin 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_9 : anycWin 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_10 : anycWin 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_11 : anycWin 11 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
