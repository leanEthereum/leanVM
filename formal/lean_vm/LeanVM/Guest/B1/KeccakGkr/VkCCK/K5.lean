/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.K5

  The kernel's checks of `verify_keccak`'s steps 10 and 11.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem step_ker_10 : stepKer 10 882 := by decide +kernel
theorem step_ker_11 : stepKer 11 923 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
