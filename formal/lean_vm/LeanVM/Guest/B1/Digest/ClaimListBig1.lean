/-
  LeanVM.Guest.B1.Digest.ClaimListBig1

  Windows 4 to 7 of `claim_list_digest`'s big frame loop `claim_list_chain_loop0`: blocks 16 to 31,
  cells 136 to 271, each window a kernel check of its own (the kernel's memory is a
  declaration's).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListDefs

namespace LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem bigWin_4 : bigWin 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_5 : bigWin 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_6 : bigWin 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem bigWin_7 : bigWin 7 = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
