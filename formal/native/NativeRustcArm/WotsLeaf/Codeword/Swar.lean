module

public import NativeRustc.Xmss.Swar
public import NativeRustcArm.Sym

/-!
# `is_codeword`'s test as the machine computes it

The executor's `ubfm x, k, 63` is `x >>> k` (`evalUBFM_lsr`); the 32-bit sum
`lowLo + lowHi + ((highLo + highHi) << 1)` compared with `106` is `is_codeword` of the digest when
its top 12 bits are zero (`swar_beq`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc.Xmss NativeRustc.Xmss.Swar

public section

theorem toNat_take'' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `ubfm x, k, 63` (`lsr x, #k`). -/
theorem evalUBFM_lsr (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (evalUBFM (w := .W64) x k 63 : BitVec 64) = x >>> k := by
  have hb : RegWidth.W64.bits = 64 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [evalUBFM, hb, Nat.mod_eq_of_lt hk, show 63 % 64 = 63 from rfl,
    show 63 ≥ k from by omega, ↓reduceIte, BitVec.toNat_setWidth, toNat_take'',
    BitVec.toNat_ushiftRight]
  have h1 : x.toNat >>> k < 2 ^ (63 - k + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 63 - k + 1 + k = 64 by omega]
    exact x.isLt
  have h2 : 2 ^ (63 - k + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

theorem evalUBFM_2 (x : BitVec 64) : (evalUBFM (w := .W64) x 2 63 : BitVec 64) = x >>> 2 :=
  evalUBFM_lsr x (by decide)

theorem evalUBFM_56 (x : BitVec 64) : (evalUBFM (w := .W64) x 56 63 : BitVec 64) = x >>> 56 :=
  evalUBFM_lsr x (by decide)

/-- The 32-bit sum `a + (b << 1)` compared with `106`, for small `a`, `b`. -/
theorem sum_beq (a b : BitVec 64) (ha : a.toNat ≤ 128) (hb : b.toNat ≤ 128) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a +
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b <<< 1)))) ==
      BitVec.setWidth 32 (106#64)) = (a.toNat + 2 * b.toNat == 106) := by
  have e : ∀ x y : BitVec 32, (x == y) = (x.toNat == y.toNat) := fun x y ↦ by
    by_cases h : x = y
    · subst h; simp
    · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (fun h' ↦ h (BitVec.eq_of_toNat_eq h'))]
  rw [e]
  have h106 : (BitVec.setWidth 32 (106#64)).toNat = 106 := rfl
  rw [h106]
  congr 1
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- A sum of two counts is their sum. -/
theorem toNat_add_small (a b : BitVec 64) (ha : a.toNat ≤ 64) (hb : b.toNat ≤ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- **The 32-bit test of the bit counts** is `is_codeword` of the digest. -/
theorem swar_beq (lo hi : BitVec 64) (h : hi.toNat < 2 ^ 52) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (popLowLo lo + popLowHi hi) +
        BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.setWidth 32 (popHighLo lo + popHighHi hi) <<< 1)))) ==
      BitVec.setWidth 32 (106#64)) = isCodeword (2 ^ 64 * hi.toNat + lo.toNat) := by
  have h1 := popLowLo_toNat lo
  have h2 := popLowHi_toNat hi h
  have h3 := popHighLo_toNat lo
  have h4 := popHighHi_toNat hi h
  have b1 := pop_le (lo.toNat &&& 0x5555555555555555) 64
  have b2 := pop_le (hi.toNat &&& 0x5555555555555555) 64
  have b3 := pop_le (lo.toNat &&& 0xaaaaaaaaaaaaaaaa) 64
  have b4 := pop_le (hi.toNat &&& 0xaaaaaaaaaaaaaaaa) 64
  have s1 := toNat_add_small (popLowLo lo) (popLowHi hi) (by omega) (by omega)
  have s2 := toNat_add_small (popHighLo lo) (popHighHi hi) (by omega) (by omega)
  rw [sum_beq _ _ (by omega) (by omega), isCodeword_swar lo hi h, s1, s2, h1, h2, h3, h4]

end

end NativeRustcArm.WotsLeafProof
