/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.K0

  The kernel's checks of `verify_keccak`'s steps 0 and 1.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem step_ker_0 : stepKer 0 448 := by decide +kernel
theorem step_ker_1 : stepKer 1 489 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
