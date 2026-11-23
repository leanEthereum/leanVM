module

public import NativeRustcVm.Field.Clmul
import NativeVm.Equiv.Field

/-!
# The product in `E`

`ewMul` (`EW::mul`) is the model's `EW.mul`: in the quotient, each limb's reduction stands for its
pair's polynomial (`toQuot_reduce`); the Karatsuba middle term `(a0 + a1)(b0 + b1) + a0 b0 + a1 b1`
is `a0 b1 + a1 b0` over `GF(2)`, and the 128-bit shift of `a1 b1` by one, its top bit clear, is its
product by `x` (`toPoly_shl1`), the model's `mulX`.
-/

namespace NativeRustcVm.Field

open Polynomial BinaryField

public section

theorem add_self_poly (p : (ZMod 2)[X]) : p + p = 0 := by
  rw [← two_mul]
  exact ZMod2Poly.two_mul p

theorem toPoly_two : toPoly (2#64) = X := by
  ext k
  rw [coeff_toPoly, coeff_X]
  by_cases hk : k < 64
  · have : ∀ k < 64, (2#64).getLsbD k = decide (k = 1) := by decide +kernel
    rw [this k hk]
    by_cases h : k = 1 <;> simp [h, zb, eq_comm]
  · rw [BitVec.getLsbD_of_ge _ k (by omega), zb_false, ite_eq_right (by omega)]

/-- A 128-bit shift by one, the top bit clear, is the product by `x`. -/
theorem toPoly_shl1 (lo hi : BitVec 64) (h : hi.getLsbD 63 = false) :
    toPoly ((hi <<< 1) ||| (lo >>> 63)) * X ^ 64 + toPoly (lo <<< 1) =
      X * (toPoly hi * X ^ 64 + toPoly lo) := by
  have e : X * (toPoly hi * X ^ 64 + toPoly lo) = toPoly hi * X ^ 65 + toPoly lo * X ^ 1 := by
    ring
  have hge : ∀ (x : BitVec 64) (n : ℕ), 64 ≤ n → x.getLsbD n = false :=
    fun x n hn ↦ BitVec.getLsbD_of_ge x n hn
  rw [e]
  ext k
  simp only [coeff_add, coeff_mul_X_pow', coeff_toPoly, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  rcases (by omega : k = 0 ∨ (1 ≤ k ∧ k < 64) ∨ k = 64 ∨ (65 ≤ k ∧ k < 128) ∨ k = 128 ∨ 128 < k)
    with h1 | h1 | h1 | h1 | h1 | h1
  · subst h1; simp [zb]
  · rw [ite_eq_right (show ¬ 64 ≤ k by omega), ite_eq_right (show ¬ 65 ≤ k by omega),
      ite_eq_left (show 1 ≤ k by omega)]
    have a1 : decide (k < 64) = true := decide_eq_true h1.2
    have a2 : decide (k < 1) = false := decide_eq_false (by omega)
    simp only [a1, a2, Bool.not_false, Bool.true_and, zero_add]
  · subst h1; simp [zb]
  · rw [ite_eq_left (show 64 ≤ k by omega), ite_eq_left (show 65 ≤ k by omega),
      ite_eq_left (show 1 ≤ k by omega), hge lo (63 + (k - 64)) (by omega), hge lo (k - 1) (by omega),
      show k - 64 - 1 = k - 65 by omega]
    have a1 : decide (k - 64 < 64) = true := decide_eq_true (by omega)
    have a2 : decide (k - 64 < 1) = false := decide_eq_false (by omega)
    have a3 : decide (k < 64) = false := decide_eq_false (by omega)
    simp only [a1, a2, a3, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false, zb_false,
      add_zero]
  · have h' : hi[63] = false := by simpa using h
    subst h1; simp [zb, h']
  · simp (disch := omega) [zb]

/-- **`EW::mul` is the model's `EW.mul`.** -/
theorem ewMul_eq (a0 a1 b0 b1 : BitVec 64) :
    ewMul a0 a1 b0 b1 =
      ((NativeVm.Model.EW.mul ⟨.ofBitVec a0, .ofBitVec a1⟩ ⟨.ofBitVec b0, .ofBitVec b1⟩).c0.toBitVec,
        (NativeVm.Model.EW.mul ⟨.ofBitVec a0, .ofBitVec a1⟩ ⟨.ofBitVec b0, .ofBitVec b1⟩).c1.toBitVec) := by
  have inj : ∀ x y : BitVec 64, BF64.toQuot (BF64.ofBitVec x) = BF64.toQuot (BF64.ofBitVec y) →
      x = y := fun x y h ↦ congrArg BF64.toBitVec (BF64.toQuot_injective h)
  have hx : ∀ x y : BitVec 64, BF64.toQuot (BF64.ofBitVec (x ^^^ y)) =
      BF64.toQuot (BF64.ofBitVec x) + BF64.toQuot (BF64.ofBitVec y) := fun x y ↦ by
    show BF64.toQuot (BF64.ofBitVec x + BF64.ofBitVec y) = _
    exact BF64.toQuot_add _ _
  have h0 := toPoly_clmul a0 b0
  have h1 := toPoly_clmul a1 b1
  have hm := toPoly_clmul (a0 ^^^ a1) (b0 ^^^ b1)
  have hs := toPoly_shl1 (clmul a1 b1).1 (clmul a1 b1).2 (by
    have := coeff_clmul_snd a1 b1 63
    rw [coeff_toPoly, coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (by
      have := natDegree_toPoly_le a1; have := natDegree_toPoly_le b1; omega))] at this
    revert this; cases (clmul a1 b1).2.getLsbD 63 <;> simp [zb])
  rw [toPoly_xor, toPoly_xor] at hm
  simp only [ewMul, NativeVm.Model.EW.mul, UInt64.toBitVec_xor, NativeVm.Equiv.mulX_eq_kmul,
    ← kmul_toBitVec, Prod.mk.injEq]
  constructor <;> apply inj <;> simp only [hx, toQuot_reduce, toQuot_kmul, toPoly_xor]
  · simp only [← map_mul, ← map_add]
    apply congrArg (AdjoinRoot.mk BF64.basePoly)
    linear_combination h0 + h1
  · rw [show AdjoinRoot.mk BF64.basePoly (toPoly (kmul a1 b1)) =
        BF64.toQuot (BF64.ofBitVec (kmul a1 b1)) from rfl, toQuot_kmul,
      show (2 : UInt64).toBitVec = 2#64 from rfl, toPoly_two]
    simp only [← map_mul, ← map_add]
    apply congrArg (AdjoinRoot.mk BF64.basePoly)
    linear_combination hm + h0 + h1 + hs + X * h1 + add_self_poly (toPoly a0 * toPoly b0) +
      add_self_poly (toPoly a1 * toPoly b1)

end

end NativeRustcVm.Field
