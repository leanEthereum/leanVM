module

public import LeanVM.Spec.Blake2s

/-!
# BLAKE2s constants

Kernel checks of `iv` and `sigma` against RFC 7693 §2.6 to §2.7, independent of the Appendix D
tables they were dumped from: every row of `sigma` is a permutation, and `iv[i]` is
`⌊2^32 · frac(√pᵢ)⌋` for the `i`-th prime `pᵢ`, stated without square roots as the pair of
inequalities that characterise the floor.
-/

namespace LeanVMTests.Parameters.Blake2s

open LeanVM.Parameters

/-- Every row of the message schedule is a permutation of the sixteen word indices. -/
example : ∀ r : Fin 10, ∀ j : Fin 16, ∃ k : Fin 16, sigma[r][k] = j := by decide

/-- The first eight primes and the integer parts of their square roots. -/
def primes : Vector (Nat × Nat) 8 :=
  #v[(2, 1), (3, 1), (5, 2), (7, 2), (11, 3), (13, 3), (17, 4), (19, 4)]

/-- RFC 7693 §2.6: with `p = pᵢ`, `q = ⌊√p⌋` and `s = 2^32 · q + iv[i]`, the word `iv[i]` is
`⌊2^32 · frac(√p)⌋` exactly when `s = ⌊√(p · 2^64)⌋`, that is `s² ≤ p · 2^64 < (s + 1)²`. -/
example : ∀ i : Fin 8,
    let p := primes[i].1
    let q := primes[i].2
    let s := 2 ^ 32 * q + iv[i].toNat
    q ^ 2 ≤ p ∧ p < (q + 1) ^ 2 ∧ s ^ 2 ≤ p * 2 ^ 64 ∧ p * 2 ^ 64 < (s + 1) ^ 2 := by
  decide

end LeanVMTests.Parameters.Blake2s
