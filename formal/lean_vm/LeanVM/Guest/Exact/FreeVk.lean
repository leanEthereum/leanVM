/-
  LeanVM.Guest.Exact.FreeVk

  `verify_keccak`'s callees with no computed hint in their subtrees are exact for free, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.CoreNames

/-!
# `verify_keccak`'s free callees

Its copy loops, its two plain rounds and its layers' two loops each have no computed hint in their subtrees
(`exactFree`), so every valid tree of one is exact on every reader (`every_exact_of_free`).
-/

namespace LeanVM.Guest.Memory

@[expose] public section

theorem vk_loop0_exactFree : ExactFreeG (name% «verify_keccak_loop0») :=
  exactFreeG_of (j := idx% «verify_keccak_loop0») (by decide +kernel)

theorem vk_loop1_exactFree : ExactFreeG (name% «verify_keccak_loop1») :=
  exactFreeG_of (j := idx% «verify_keccak_loop1») (by decide +kernel)

theorem vk_loop2_exactFree : ExactFreeG (name% «verify_keccak_loop2») :=
  exactFreeG_of (j := idx% «verify_keccak_loop2») (by decide +kernel)

theorem plain0_exactFree : ExactFreeG (name% «keccak_plain_rounds__L6_L0») :=
  exactFreeG_of (j := idx% «keccak_plain_rounds__L6_L0») (by decide +kernel)

theorem plain1_exactFree : ExactFreeG (name% «keccak_plain_rounds__L4_L1») :=
  exactFreeG_of (j := idx% «keccak_plain_rounds__L4_L1») (by decide +kernel)

theorem layer0_loop0_exactFree : ExactFreeG (name% «keccak_layer__L0_loop0») :=
  exactFreeG_of (j := idx% «keccak_layer__L0_loop0») (by decide +kernel)

theorem layer0_loop1_exactFree : ExactFreeG (name% «keccak_layer__L0_loop1») :=
  exactFreeG_of (j := idx% «keccak_layer__L0_loop1») (by decide +kernel)

theorem layer1_loop0_exactFree : ExactFreeG (name% «keccak_layer__L1_loop0») :=
  exactFreeG_of (j := idx% «keccak_layer__L1_loop0») (by decide +kernel)

theorem layer1_loop1_exactFree : ExactFreeG (name% «keccak_layer__L1_loop1») :=
  exactFreeG_of (j := idx% «keccak_layer__L1_loop1») (by decide +kernel)

end
end LeanVM.Guest.Memory
