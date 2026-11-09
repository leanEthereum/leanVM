/-
  LeanVM.Guest.B1.Digest.Mono2

  Windows 8–11 of `child_claim_list_mono`'s big frame loop `__loop19`: blocks
  32–47, claims 72–107, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.MonoDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem monoWin_8 : monoWinOk 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_9 : monoWinOk 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_10 : monoWinOk 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_11 : monoWinOk 11 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
