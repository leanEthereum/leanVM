/-
  LeanVM.Guest.B1.Digest.Mono1

  Windows 4–7 of `child_claim_list_mono`'s big frame loop `__loop19`: blocks
  16–31, claims 36–71, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.MonoDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem monoWin_4 : monoWinOk 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_5 : monoWinOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_6 : monoWinOk 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_7 : monoWinOk 7 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
