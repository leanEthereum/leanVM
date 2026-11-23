module

public import NativeRustcX64.Sym

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): the arithmetic of its counts and padding

`len < 2 ^ 32` here, and rustc computes at 32 bits: the whole blocks' count `len / 136` as `len`
times `⌈2 ^ 39 / 136⌉` shifted right by 39 (`nb_val`); `17 nb` as `nb + (nb << 4)` at 32 bits
(`nb17_val`); the bytes past the whole blocks `len - (128 nb + 8 nb)` (`rem_val`); the padded
lane's offset `r & 248` (`and248_val`).
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym

public section

theorem toNat_trunc32 (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [UnOp.apply, toNat_ext, toNat_low, Width.bits]

theorem toNat_add64 (x y : BitVec 64) :
    (BinOp.apply .add .W64 x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]

theorem toNat_mul64 (x y : BitVec 64) :
    (BinOp.apply .mul .W64 x y).toNat = x.toNat * y.toNat % 2 ^ 64 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul]

theorem toNat_shr64 (x : BitVec 64) {n : Nat} (hn : n < 64) :
    (BinOp.apply .shr .W64 x (BitVec.ofNat 64 n)).toNat = x.toNat / 2 ^ n := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 n) = n := by
    simp only [shiftCount, shiftMask, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem toNat_shl32 (x : BitVec 64) {n : Nat} (hn : n < 32) :
    (BinOp.apply .shl .W32 x (BitVec.ofNat 64 n)).toNat = x.toNat % 2 ^ 32 * 2 ^ n % 2 ^ 32 := by
  have hs : shiftCount .W32 (BitVec.ofNat 64 n) = n := by
    simp only [shiftCount, shiftMask, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 5) (by omega)
  simp only [BinOp.apply, hs, toNat_ext, BitVec.toNat_shiftLeft, toNat_low, Nat.shiftLeft_eq,
    Width.bits]

theorem toNat_sub32 (x y : BitVec 64) :
    (BinOp.apply .sub .W32 x y).toNat = (2 ^ 32 - y.toNat % 2 ^ 32 + x.toNat % 2 ^ 32) % 2 ^ 32 := by
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_sub, toNat_low, Width.bits]

/-- **The whole blocks' count**, for `len < 2 ^ 32`. -/
theorem nb_val {len : Nat} (h : len < 2 ^ 32) :
    BinOp.apply .shr .W64 (BinOp.apply .mul .W64 (BitVec.ofNat 64 4042322161)
      (UnOp.apply .trunc .W32 (BitVec.ofNat 64 len))) (BitVec.ofNat 64 39) =
      BitVec.ofNat 64 (len / 136) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shr64 _ (by decide), toNat_mul64, toNat_trunc32, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have e1 : len % 2 ^ 64 % 2 ^ 32 = len := by omega
  have e2 : 4042322161 % 2 ^ 64 = 4042322161 := rfl
  have e3 : 4042322161 * len % 2 ^ 64 = 4042322161 * len := Nat.mod_eq_of_lt (by omega)
  have e4 : len / 136 % 2 ^ 64 = len / 136 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, e4]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 136 ∧ len = 136 * q + r :=
    ⟨len / 136, len % 136, Nat.mod_lt _ (by decide), (Nat.div_add_mod len 136).symm⟩
  have hq : q < 2 ^ 25 := by omega
  rw [show 4042322161 * (136 * q + r) = 2 ^ 39 * q + (8 * q + 4042322161 * r) by omega,
    Nat.mul_add_div (by decide), Nat.div_eq_of_lt (by omega)]
  omega

/-- **`17 nb`**, `nb + (nb << 4)` at 32 bits. -/
theorem nb17_val {nb : Nat} (h : nb < 2 ^ 27) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 nb) (BinOp.apply .shl .W32
      (UnOp.apply .trunc .W32 (BitVec.ofNat 64 nb)) (BitVec.ofNat 64 4)) =
      BitVec.ofNat 64 (17 * nb) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add64, toNat_shl32 _ (by decide), toNat_trunc32, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have e1 : nb % 2 ^ 64 = nb := Nat.mod_eq_of_lt (by omega)
  have e2 : nb % 2 ^ 32 = nb := Nat.mod_eq_of_lt (by omega)
  have e3 : nb * 2 ^ 4 % 2 ^ 32 = 16 * nb := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have e4 : (nb + 16 * nb) % 2 ^ 64 = 17 * nb := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have e5 : 17 * nb % 2 ^ 64 = 17 * nb := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e2, e3, e4, e5]

/-- **The bytes past the whole blocks**, `len - 136 nb` at 32 bits. -/
theorem rem_val {len : Nat} (h : len < 2 ^ 32) :
    BinOp.apply .sub .W32 (BitVec.ofNat 64 len) (UnOp.apply .trunc .W32 (BinOp.apply .add .W64
      (BinOp.apply .shl .W32 (BitVec.ofNat 64 (len / 136)) (BitVec.ofNat 64 7))
      (BinOp.apply .mul .W64 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 (len / 136)))
        (BitVec.ofNat 64 8)))) = BitVec.ofNat 64 (len % 136) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sub32, toNat_trunc32, toNat_add64, toNat_shl32 _ (by decide), toNat_mul64,
    toNat_trunc32, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 136 ∧ len = 136 * q + r :=
    ⟨len / 136, len % 136, Nat.mod_lt _ (by decide), (Nat.div_add_mod len 136).symm⟩
  have hq : q < 2 ^ 25 := by omega
  have e0 : (136 * q + r) / 136 = q := by omega
  have e0' : (136 * q + r) % 136 = r := by omega
  rw [e0, e0']
  have e1 : q % 2 ^ 64 = q := Nat.mod_eq_of_lt (by omega)
  have e2 : q % 2 ^ 32 = q := Nat.mod_eq_of_lt (by omega)
  have e3 : q * 2 ^ 7 % 2 ^ 32 = 128 * q := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have e4 : q * (8 % 2 ^ 64) % 2 ^ 64 = 8 * q := by
    rw [show 8 % 2 ^ 64 = 8 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  have e5 : (128 * q + 8 * q) % 2 ^ 64 % 2 ^ 32 = 136 * q := by
    rw [show 128 * q + 8 * q = 136 * q by omega, Nat.mod_eq_of_lt (show 136 * q < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 136 * q < 2 ^ 32 by omega)]
  have e6 : (136 * q + r) % 2 ^ 64 % 2 ^ 32 = 136 * q + r := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e7 : r % 2 ^ 64 = r := Nat.mod_eq_of_lt (by omega)
  have e8 : 136 * q % 2 ^ 32 = 136 * q := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, e4, e5, e6, e7, e8, show 2 ^ 32 - 136 * q + (136 * q + r) = r + 2 ^ 32 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The padded lane's offset, `r & 248`. -/
theorem and248_val : ∀ r < 136,
    BinOp.apply .and .W32 (BitVec.ofNat 64 r) (BitVec.ofNat 64 248) =
      BitVec.ofNat 64 (8 * (r / 8)) := by
  decide +kernel

end

end NativeRustcVmX64.WordsIv
