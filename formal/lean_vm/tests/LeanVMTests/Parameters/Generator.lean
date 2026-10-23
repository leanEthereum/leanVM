module

public import LeanVM.Parameters.Generator
meta import LeanVM.Parameters.Generator

/-!
# Tests: the generator

`gpow k` is bit `k` for `k < 64`, pinning `g = x`, and `gpow 64` is the reduction tail
`x^4 + x^3 + x + 1 = K.ofBits 0x1b` of the modulus (`crates/primitives/src/field/gf2_64.rs:14`,
`R64`). Nearby false statements follow: `g^3` has order
`(2^64 - 1)/3` and fails the `3`-check, and `gpow` wraps at the order.
-/

namespace LeanVMTests.Parameters

open LeanVM.Parameters

public section

/-! ## `g = x` -/

#guard gpow 0 = 1
#guard gpow 1 = g
#guard (List.range 64).all fun k ↦ gpow k = BF64.ofBitVec (1#64 <<< k)
#guard gpow 64 = K.ofBits 0x1b

/-- `gpow k` is bit `k` for `k < 64`, checked in the kernel. -/
example : ∀ k < 64, gpow k = BF64.ofBitVec (1#64 <<< k) := by decide +kernel

/-! ## Nearby false statements -/

/-- `g^3` fails the `3`-check: its order divides `(2^64 - 1)/3`, so addresses `(g^3)^i` and
`(g^3)^(i + (2^64 - 1)/3)` would collide. The check is load-bearing. -/
example : (g ^ 3) ^ ((2 ^ 64 - 1) / 3) = 1 := by decide +kernel

/-- `gpow` wraps at the order: `g^(2^64 - 1) = g^0`. -/
example : gpow (2 ^ 64 - 1) = gpow 0 := by
  show g ^ (2 ^ 64 - 1) = g ^ 0
  rw [pow_zero]
  exact g_pow_card_sub_one

end
end LeanVMTests.Parameters
