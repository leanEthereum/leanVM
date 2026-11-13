/-
  LeanVM.Guest.B1.Digest.ChildListCW0

  `child_claim_list_any`'s big frame loop `child_claim_list_any_loop0`, its records evaluated by windows of nine
  (windows 0–3), each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem anycWin_0 : anycWin 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_1 : anycWin 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_2 : anycWin 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anycWin_3 : anycWin 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
