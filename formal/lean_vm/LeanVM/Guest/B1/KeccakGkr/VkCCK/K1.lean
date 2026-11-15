/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.K1

  The kernel's checks of `verify_keccak`'s steps 2 and 3.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem step_ker_2 : stepKer 2 525 := by decide +kernel
theorem step_ker_3 : stepKer 3 559 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
