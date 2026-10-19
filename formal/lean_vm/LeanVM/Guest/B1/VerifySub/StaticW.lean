/-
  LeanVM.Guest.B1.VerifySub.StaticW

  The weights of `verify_sub`'s statically bounded callees at one frame weight.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# `verify_sub`'s static callees' weights

`VsStat`: a weight for each of `g_power_of_word__L6`, the two `log2_ceil_in_the_exponent` arms,
`assert_canonical`, `certify_placement` and `open_stacked`; `VsStatOk ω c`: every valid tree of each
weighs at most its weight at `ω`, `open_stacked` at every configuration.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The weights of `verify_sub`'s statically bounded callees. -/
structure VsStat where
  gpw : ℕ
  l2a : ℕ
  l2b : ℕ
  ac : ℕ
  pl : ℕ
  os : ℕ

/-- **Every valid tree of `verify_sub`'s statically bounded callees is within `c` at `ω`.** -/
structure VsStatOk (ω : String → ℕ) (c : VsStat) : Prop where
  gpw : WeightLe coreProgram ω "g_power_of_word__L6" fun _ => c.gpw
  l2a : WeightLe coreProgram ω "log2_ceil_in_the_exponent__L0_L34" fun _ => c.l2a
  l2b : WeightLe coreProgram ω "log2_ceil_in_the_exponent__L15_L34" fun _ => c.l2b
  ac : WeightLe coreProgram ω "assert_canonical" fun _ => c.ac
  pl : WeightLe coreProgram ω "certify_placement" fun _ => c.pl
  os : ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 → WeightLe coreProgram ω (openName μ r) fun _ => c.os

end
end LeanVM.Guest.B1.VerifySub
