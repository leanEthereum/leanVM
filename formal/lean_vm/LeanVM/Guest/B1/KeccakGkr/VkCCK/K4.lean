/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.K4

  The kernel's checks of `verify_keccak`'s steps 8 and 9.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem step_ker_8 : stepKer 8 759 := by decide +kernel
theorem step_ker_9 : stepKer 9 797 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
