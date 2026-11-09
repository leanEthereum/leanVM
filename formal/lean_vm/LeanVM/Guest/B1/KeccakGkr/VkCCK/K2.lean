/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.K2

  The kernel's checks of `verify_keccak`'s steps 4 and 5.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem step_ker_4 : stepKer 4 643 := by decide +kernel
theorem step_ker_5 : stepKer 5 684 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
