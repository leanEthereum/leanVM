/-
  LeanVM.Guest.B1.Digest.ClaimListBig0

  Windows 0–3 of `claim_list_digest`'s big frame loop `__loop15`: blocks 0–15,
  cells 0–135, each window a kernel check of its own (the kernel's memory is a
  declaration's: about 2 GB a window).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem bigWin_0 : bigWin 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_1 : bigWin 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_2 : bigWin 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_3 : bigWin 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
