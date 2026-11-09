/-
  LeanVM.Guest.B1.Digest.Mono3

  Windows 12–15 of `child_claim_list_mono`'s big frame loop `__loop19`: blocks
  48–63, claims 108–135, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.MonoDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem monoWin_12 : monoWinOk 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_13 : monoWinOk 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_14 : monoWinOk 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_15 : monoWinOk 15 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
