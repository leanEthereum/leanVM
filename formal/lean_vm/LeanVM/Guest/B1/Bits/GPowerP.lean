/-
  LeanVM.Guest.B1.Bits.GPowerP

  B1 for `g_power_of_word`, for any program that finds it: an integer word below `2^6` raised to
  its g-power. It reads `g_power_of_word`'s core module only.
-/

module

public import LeanVM.Guest.B1.Bits.MeaningP
import LeanVM.Guest.B1.Common.Vc
public import LeanVM.Guest.Pack.P41.Core

/-!
# `g_power_of_word` (TRIAGE #17)

`g_power_of_word(value)` hints the six bits of `value`, pins each by booleanity (`b = b·b`),
accumulates the word `Σ b_j·2^j` and the product `Π (1 + b_j·(1 + g^(2^j)))`, the constants
folded (`1 + g^(2^j)` the word `2^(2^j) + 1`), and asserts the word is `value`. So
`value = E(n)`, `n < 2^6`, and the function returns `g^n` (`g_power_of_word_spec`, from the
condition `vc` computes). `g_power_of_word_holdsP` holds for any program that finds the function
(`Finds`); `GPower.lean` instantiates it at `coreProgram`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The folded factor constant `1 + g^(2^j)`. -/
theorem word_gpow_one (j : ℕ) (hj : 2 ^ j < 64) (c : ℕ) (hc : c = 2 ^ 2 ^ j ^^^ 1) :
    word c 0 = gen ^ 2 ^ j + 1 := by
  rw [word_eOfNat, gen_pow_eq_eOfNat hj, ← eOfNat_one, ← eOfNat_xor, hc]

/-- **`g_power_of_word`'s core IR is its meaning**, in any program that finds it. -/
theorem g_power_of_word_holdsP (P : Program) [Finds P "g_power_of_word" Fn.«g_power_of_word».core] :
    g_power_of_word_SpecP P := by
  intro rd args rets
  rw [rel_iff_fnSem (Finds.find (P := P) (fn := Fn.«g_power_of_word».core))]
  rcases args with _ | ⟨v, _ | ⟨_, _⟩⟩ <;>
    vc [word_one, word_gpow_one 0 (by norm_num) 3 (by decide),
      word_gpow_one 1 (by norm_num) 5 (by decide), word_gpow_one 2 (by norm_num) 17 (by decide),
      word_gpow_one 3 (by norm_num) 257 (by decide), word_gpow_one 4 (by norm_num) 65537 (by decide),
      word_gpow_one 5 (by norm_num) 4294967297 (by decide)] <;>
    simp only [MeaningGPowerOfWord]
  have hw (b : ℕ → E) : ∑ j ∈ Finset.range 6, b j * eOfNat (2 ^ j) =
      b 0 + b 1 * word 2 0 + b 2 * word 4 0 + b 3 * word 8 0 + b 4 * word 16 0 + b 5 * word 32 0 := by
    simp [Finset.sum_range_succ, word_eOfNat, eOfNat_one]
  constructor
  · rintro ⟨b0, h0, b1, h1, b2, h2, b3, h3, b4, h4, b5, h5, hs, rfl⟩
    let b : ℕ → E := fun j => [b0, b1, b2, b3, b4, b5].getD j 0
    obtain ⟨hK, hlt, hprod⟩ := g_power_of_word_spec (n := 6) (b := b) (value := v) (by norm_num)
      (fun j hj => by interval_cases j <;> simp [b, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5])
      (by rw [hw]; exact e_add_eq_zero_iff.mp hs)
    refine ⟨kToNat (v.limb 0), hlt, by rw [eOfNat, ofBits_kToNat]; exact eq_ofK_limb hK, ?_⟩
    rw [← hprod]
    simp [Finset.prod_range_succ, b]
  · rintro ⟨n, hn, rfl, rfl⟩
    have hpr := prod_bitE_gen_pow n.testBit 6
    rw [bitsVal_testBit hn] at hpr
    have hsum := reconstruct_bits 0 hn
    simp only [Nat.pow_zero, Nat.one_mul, eOfNat128_of_lt (show n < 2 ^ 64 by omega)] at hsum
    refine ⟨_, (bitE_mul_self (n.testBit 0)).symm, _, (bitE_mul_self (n.testBit 1)).symm,
      _, (bitE_mul_self (n.testBit 2)).symm, _, (bitE_mul_self (n.testBit 3)).symm,
      _, (bitE_mul_self (n.testBit 4)).symm, _, (bitE_mul_self (n.testBit 5)).symm, ?_, ?_⟩
    · rw [e_add_eq_zero_iff, ← hw (fun j => bitE (n.testBit j)), ← hsum]
      simp [Finset.sum_range_succ, coordBasis, eOfNat128_of_lt]
    · rw [← hpr]
      simp [Finset.prod_range_succ]

end
end LeanVM.Guest.B1
