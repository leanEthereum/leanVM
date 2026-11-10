import Rv64Verifier.Proofs.Common

/-!
# `len / 136 * 136` as `keccak_hash` computes it

`data.as_chunks::<136>()` divides by `mulhu` with `0xf0f0f0f0f0f0f0f1` (`17 * C = 2^68 + 1`) and two
masks: `div136` says it is the length of the whole blocks.
-/

namespace Rv64Verifier.Hash
open RiscvZkvm.Rv64

theorem land_high (n k : Nat) (hn : n < 2 ^ 64) (hk : k ≤ 64) :
    n &&& (2 ^ 64 - 2 ^ k) = n / 2 ^ k * 2 ^ k := by
  have h1 : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hk, Nat.one_mul]
  have h2 : n / 2 ^ k * 2 ^ k = (n >>> k) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [h1, h2]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : k ≤ i
  · by_cases h64 : i < 64
    · simp [hi, show i - k < 64 - k by omega, Nat.add_sub_cancel' hi]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, show ¬ i - k < 64 - k by omega, Nat.add_sub_cancel' hi, this]
  · simp [hi]

theorem toNat_mulhu (x y : Word) : (rv64_mulhu x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hx := x.isLt
  have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by norm_num
  have hq : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc x.toNat * y.toNat < 2 ^ 128 := hxy
      _ = 2 ^ 64 * 2 ^ 64 := by norm_num
  simp only [rv64_mulhu, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show y.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt hxy, Nat.mod_eq_of_lt hq]

theorem div_magic (x : Nat) (hx : x < 2 ^ 64) :
    x * 17361641481138401521 / 2 ^ 64 / 128 = x / 136 := by
  rw [Nat.div_div_eq_div_mul]
  have h := Nat.div_add_mod x 136
  have hr := Nat.mod_lt x (show 136 > 0 by decide)
  generalize x / 136 = q at h ⊢
  generalize x % 136 = r at h hr
  subst h
  apply Nat.div_eq_of_lt_le <;> omega

/-- **The whole blocks' length.** -/
theorem div136 (x : Word) :
    (rv64_mulhu x 0xf0f0f0f0f0f0f0f1 &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ 7)) +
      ((rv64_mulhu x 0xf0f0f0f0f0f0f0f1 >>> 4) &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ 3)) =
      BitVec.ofNat 64 (136 * (x.toNat / 136)) := by
  have hx := x.isLt
  have hm := toNat_mulhu x 0xf0f0f0f0f0f0f0f1
  have hc : (0xf0f0f0f0f0f0f0f1 : Word).toNat = 17361641481138401521 := rfl
  rw [hc] at hm
  generalize rv64_mulhu x 0xf0f0f0f0f0f0f0f1 = m at hm ⊢
  have hmlt := m.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 64 - 2 ^ 7 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show 2 ^ 64 - 2 ^ 3 < 2 ^ 64 by decide),
    land_high _ _ hmlt (by decide), land_high _ _ (by rw [Nat.shiftRight_eq_div_pow]; omega)
      (by decide), Nat.shiftRight_eq_div_pow]
  have e1 : m.toNat / 2 ^ 4 / 2 ^ 3 = m.toNat / 2 ^ 7 := by rw [Nat.div_div_eq_div_mul]; rfl
  have e2 : m.toNat / 2 ^ 7 = x.toNat / 136 := by rw [hm]; exact div_magic _ hx
  rw [e1, e2]
  omega

end Rv64Verifier.Hash
