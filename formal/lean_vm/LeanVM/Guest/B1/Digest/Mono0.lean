/-
  LeanVM.Guest.B1.Digest.Mono0

  Windows 0–3 of `child_claim_list_mono`'s big frame loop `child_claim_list_mono_loop0`: blocks
  0–15, claims 0–35, each window a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.MonoDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem monoWin_0 : monoWinOk 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_1 : monoWinOk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_2 : monoWinOk 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoWin_3 : monoWinOk 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
