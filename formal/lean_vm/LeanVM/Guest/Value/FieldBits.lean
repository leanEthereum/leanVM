/-
  LeanVM.Guest.Value.FieldBits

  Words of `K` as bit strings: characteristic two, and products by powers of `x` that do not reduce.
-/

module

public import LeanVM.Parameters.Field

/-!
# Field words as bits

`E` has characteristic two (`e_add_eq_zero_iff`); the word `2^s · v` of degree below `64` is the
product of the words `2^s` and `v` (`ofBits_two_pow_mul`), so `g^a` is the word `2^a`
(`g_pow_eq_ofBits`). Apart from `Value/Tower.lean`, which imports this module, so that the guest's
memory-layer certificates, which read these facts, do not import the verifier's statement.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters

@[expose] public section

/-- In `E`, `a + b = 0` exactly when `a = b`. -/
theorem e_add_eq_zero_iff {a b : E} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

theorem ofBits_zero : K.ofBits 0 = 0 := rfl

/-- The word `2^s` is `1 <<< s`. -/
private theorem ofNat_two_pow_mul {s v : ℕ} :
    BitVec.ofNat 64 (2 ^ s * v) = BitVec.ofNat 64 v <<< s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_mul_mod, Nat.mul_comm]

/-- **No reduction**: `x^s · v` for `v` of degree below `64 - s` is the shifted word, the
product the guest's query positions (`decode_query_bits`, G:738-782) rely on. -/
theorem ofBits_two_pow_mul {s v : ℕ} (h : 2 ^ s * v < 2 ^ 64) :
    K.ofBits (2 ^ s) * K.ofBits v = K.ofBits (2 ^ s * v) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [ofBits_zero, mul_zero, Nat.mul_zero, ofBits_zero]
  have hs : s < 64 := by
    by_contra hs
    have : 2 ^ 64 ≤ 2 ^ s * v :=
      le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hs)) (Nat.le_mul_of_pos_right _ hv)
    omega
  apply BF64.toQuot_injective
  rw [BF64.toQuot_mul]
  simp only [BF64.toQuot, BF64.toPolyBF64, K.ofBits, BF64.toBitVec_ofBitVec, ofNat_two_pow_mul]
  have hx : BinaryField.toPoly (BitVec.ofNat 64 (2 ^ s)) = Polynomial.X ^ s := by
    have := BinaryField.toPoly_one_shiftLeft (w := 64) s hs
    rw [Nat.one_shiftLeft] at this
    exact this
  rw [hx, ← map_mul,
    BinaryField.toPoly_shiftLeft_no_overflow (d := 64 - s) (BitVec.ofNat 64 v) ?_ (by omega),
    mul_comm]
  rw [BitVec.toNat_ofNat]
  have : v < 2 ^ (64 - s) := by
    have h2 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
    rw [h2] at h
    exact Nat.lt_of_mul_lt_mul_left h
  exact lt_of_le_of_lt (Nat.mod_le _ _) this

/-- `g^a` is the word `2^a` below the first reduction. -/
theorem g_pow_eq_ofBits {a : ℕ} (h : a < 64) : g ^ a = K.ofBits (2 ^ a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ', ih (by omega), g, show K.ofBits 0x2 = K.ofBits (2 ^ 1) from rfl,
      ofBits_two_pow_mul (by rw [← pow_add]; exact Nat.pow_lt_pow_right (by decide) (by omega)),
      ← pow_add, add_comm]

end
end LeanVM.Guest.Value
