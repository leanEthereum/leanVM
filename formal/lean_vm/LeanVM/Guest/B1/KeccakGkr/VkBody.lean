/-
  LeanVM.Guest.B1.KeccakGkr.VkBody

  `verify_keccak`'s body is the template `vkT`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkT

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem vk_body : Data.core12.body = vkT := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.VerifySub
