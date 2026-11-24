/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK

  `verify_keccak`'s steps: the kernel's checks of their cores.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **What the kernel checks of each of the twelve steps' cores** (`stepKer`, `VkCCK/Steps.lean`), in one
evaluation, which computes the body's stores once. -/
theorem step_ker : ∀ s < 12, stepKer s (stepB s) := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
