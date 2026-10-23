/-
  LeanVM.Parameters.Generator

  The order of the generator `g = x` of `K^×` (`LeanVM.Spec.Field`): a kernel-checked
  certificate, and what exponent addressing needs of it.
-/

module

public import LeanVM.Parameters.Field
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime

/-!
# The generator `g` and exponent addressing

`g = x`, the word
`0x2`, is transcribed from `crates/primitives/src/field/gf2_64.rs:25` (`F64::G = F64(2)`, "with
`ord(x) = 2^64 - 1`") at leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, cross-checked
against `python-verifier/verifier.py:182` (`GEN = E(2)`). Specification §2
(`02-vm-specification.tex:12`) fixes a generator of `K^×` of order `2^64 - 1` without naming it.
The value appears exactly once, in `g` (`LeanVM.Spec.Field`), and is symbolic everywhere else.

The order is certified, not asserted. `|K^×| = 2^64 - 1 = 3·5·17·257·641·65537·6700417`;
`g^(2^64-1) = 1` is Lagrange (`FiniteField.pow_card_sub_one_eq_one` with `BF64.card_bf64`); and
`g^((2^64-1)/p) ≠ 1` for each of the seven primes is a `decide +kernel` on CompPoly's computable
arithmetic. Mathlib's `orderOf_eq_of_pow_and_pow_div_prime` turns these into
`orderOf g = 2^64 - 1`, hence `gpow_injOn`: addresses `g^i` and `g^j` with `i, j < 2^64 - 1`
collide only when `i = j`. An element of smaller order passes six of
the seven checks; `tests/LeanVMTests/Parameters/Generator.lean` exhibits `g^3` failing the
seventh.

Memory addresses and operands of later layers are `K` elements `gpow i = g ^ i`; `0` is never an
address (`gpow_ne_zero`), and the fall-through successor of `pc` is `g * pc` (`gpow_succ`).
-/

namespace LeanVM.Parameters

@[expose] public section

/-! ## The order certificate -/

/-- `|K^×| = 2^64 - 1`, factored into its seven primes. -/
theorem card_sub_one_factorization :
    (2 : ℕ) ^ 64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 := by norm_num

/-- `g` is nonzero, so it lies in `K^×`. -/
theorem g_ne_zero : g ≠ 0 := by decide

/-- Lagrange: `g^(2^64-1) = 1`. -/
theorem g_pow_card_sub_one : g ^ (2 ^ 64 - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one g g_ne_zero
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h

/-- The prime-`3` check of the certificate. -/
theorem g_pow_div_three_ne_one : g ^ ((2 ^ 64 - 1) / 3) ≠ 1 := by decide +kernel

/-- The prime-`5` check of the certificate. -/
theorem g_pow_div_five_ne_one : g ^ ((2 ^ 64 - 1) / 5) ≠ 1 := by decide +kernel

/-- The prime-`17` check of the certificate. -/
theorem g_pow_div_seventeen_ne_one : g ^ ((2 ^ 64 - 1) / 17) ≠ 1 := by decide +kernel

/-- The prime-`257` check of the certificate. -/
theorem g_pow_div_257_ne_one : g ^ ((2 ^ 64 - 1) / 257) ≠ 1 := by decide +kernel

/-- The prime-`641` check of the certificate. -/
theorem g_pow_div_641_ne_one : g ^ ((2 ^ 64 - 1) / 641) ≠ 1 := by decide +kernel

/-- The prime-`65537` check of the certificate. -/
theorem g_pow_div_65537_ne_one : g ^ ((2 ^ 64 - 1) / 65537) ≠ 1 := by decide +kernel

/-- The prime-`6700417` check of the certificate. -/
theorem g_pow_div_6700417_ne_one : g ^ ((2 ^ 64 - 1) / 6700417) ≠ 1 := by decide +kernel

/-- `g` generates `K^×`: its order is exactly `2^64 - 1`. -/
theorem orderOf_g : orderOf g = 2 ^ 64 - 1 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) g_pow_card_sub_one
    fun p hp hdvd ↦ ?_
  rw [card_sub_one_factorization] at hdvd
  simp only [Nat.Prime.dvd_mul hp, or_assoc] at hdvd
  rcases hdvd with h | h | h | h | h | h | h <;>
    rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]
  exacts [g_pow_div_three_ne_one, g_pow_div_five_ne_one, g_pow_div_seventeen_ne_one,
    g_pow_div_257_ne_one, g_pow_div_641_ne_one, g_pow_div_65537_ne_one,
    g_pow_div_6700417_ne_one]

/-! ## Exponent addressing -/

/-- Distinct indices below `2^64 - 1` are distinct addresses. -/
theorem gpow_injOn : Set.InjOn gpow (Set.Iio (2 ^ 64 - 1)) := by
  rw [← orderOf_g]
  exact pow_injOn_Iio_orderOf

/-- The fall-through successor: `g ^ (i + 1) = g · g ^ i`. -/
theorem gpow_succ (i : ℕ) : gpow (i + 1) = g * gpow i := pow_succ' g i

/-- `0` is not an address: no power of `g` vanishes. -/
theorem gpow_ne_zero (i : ℕ) : gpow i ≠ 0 := pow_ne_zero i g_ne_zero

end
end LeanVM.Parameters
