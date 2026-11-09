/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.K3

  The kernel's checks of `verify_keccak`'s steps 6 and 7.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem step_ker_6 : stepKer 6 727 := by decide +kernel
theorem step_ker_7 : stepKer 7 760 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
