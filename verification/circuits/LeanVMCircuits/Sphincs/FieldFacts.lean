module

public import LeanVMCircuits.Xmss.FieldFacts
public import LeanVMCircuits.Sphincs.Circuit

@[expose] public section

/-!
# The leanSPHINCS digit target in `K`

The encoding's digits sum to 191 because the circuit holds their product to `targetWord`: here `targetWord` is
`x^191`, and an exponent at most 294 reaching `x^191` is 191 (`x` has order above 195,
`Xmss.root_pow_ne_one`).
-/

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec
open LeanVMCircuits.Xmss (ofWord_eq_ev root_pow_ne_one root_ne_zero)

/-- `targetWord` is `x^191`: `x^128 · x^32 · x^16 · x^8 · x^4 · x^2 · x`. -/
theorem target_eq : ofWord Circuit.targetWord = root ^ 191 := by
  have h : Rec.mul (Rec.mul (Rec.mul (Rec.mul (Rec.mul (Rec.mul (chain.getD 7 0) (chain.getD 5 0)) (chain.getD 4 0))
      (chain.getD 3 0)) (chain.getD 2 0)) (chain.getD 1 0)) (chain.getD 0 0) = 0x8000000000000ed6 := by
    decide +kernel
  have hl : ∀ k < 64, chain.getD k 0 < 2 ^ 64 := fun k hk => (chain_squares k hk).2
  rw [Circuit.targetWord, ofWord_eq_ev _ (by norm_num), ← h, ev_mul _ _ (hl 0 (by omega)),
    ev_mul _ _ (hl 1 (by omega)), ev_mul _ _ (hl 2 (by omega)), ev_mul _ _ (hl 3 (by omega)),
    ev_mul _ _ (hl 4 (by omega)), ev_mul _ _ (hl 5 (by omega)), ev_chain 7 (by omega), ev_chain 5 (by omega),
    ev_chain 4 (by omega), ev_chain 3 (by omega), ev_chain 2 (by omega), ev_chain 1 (by omega),
    ev_chain 0 (by omega)]
  ring

/-- An exponent at most 294 with `x^a = x^191` is 191. -/
theorem eq_191 (a : ℕ) (ha : a ≤ 294) (h : root ^ a = root ^ 191) : a = 191 := by
  have hz : ∀ n, root ^ n ≠ 0 := fun n => pow_ne_zero n root_ne_zero
  rcases lt_trichotomy a 191 with hlt | heq | hgt
  · exfalso
    have : root ^ a * root ^ (191 - a) = root ^ a * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, h]
    exact root_pow_ne_one (191 - a) (by omega) (by omega) (mul_left_cancel₀ (hz a) this)
  · exact heq
  · exfalso
    have : root ^ 191 * root ^ (a - 191) = root ^ 191 * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one, h]
    exact root_pow_ne_one (a - 191) (by omega) (by omega) (mul_left_cancel₀ (hz 191) this)

end LeanVMCircuits.Sphincs
