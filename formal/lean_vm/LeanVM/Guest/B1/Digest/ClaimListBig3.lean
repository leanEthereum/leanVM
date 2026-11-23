/-
  LeanVM.Guest.B1.Digest.ClaimListBig3

  Windows 12 to 15 of `claim_list_digest`'s big frame loop `claim_list_chain_loop0`: blocks 48 to 63,
  cells 408 to 543, each window a kernel check of its own (the kernel's memory is a
  declaration's).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem bigWin_12 : bigWin 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_13 : bigWin 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_14 : bigWin 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_15 : bigWin 15 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
