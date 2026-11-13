/-
  LeanVM.Guest.B1.Digest.ClaimListBig2

  Windows 8–11 of `claim_list_digest`'s big frame loop `claim_list_digest_loop0`: blocks 32–47,
  cells 272–407, each window a kernel check of its own (the kernel's memory is a
  declaration's: about 2 GB a window).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem bigWin_8 : bigWin 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_9 : bigWin 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_10 : bigWin 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_11 : bigWin 11 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
