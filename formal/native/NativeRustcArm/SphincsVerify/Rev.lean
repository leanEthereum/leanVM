module

public import NativeRustcArm.Sym.Simp
public import NativeRustc.Sphincs.Model

/-!
# The bytes of stored values and of `rev`

A value's low bytes are its `u64`'s or `u32`'s (`byteOf_eq_toUInt64`, `byteOf_eq_toUInt32`): an
8-byte store writes `wordBytes` of it (`bytes_word`). `REV` reverses a value's bytes
(`byteOf_rev64`, `byteOf_rev32`): stored, a reversed value is its big-endian bytes
(`bytes_rev64`, `bytes_rev32`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustcArm.Sym NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

public section

/-- Two bytes of values are equal when their bits are. -/
theorem byteOf_eq_of_getLsbD {x y : BitVec 64} {t u : Nat}
    (h : ∀ j < 8, x.getLsbD (8 * t + j) = y.getLsbD (8 * u + j)) : byteOf x t = byteOf y u := by
  rw [byteOf_mod, byteOf_mod]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and]
    have := h j hj
    rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat] at this
    rwa [Nat.add_comm j, Nat.add_comm j]
  · simp [hj]

theorem revW64_getLsbD (x : BitVec 64) (i : Nat) (hi : i < 64) :
    (revW .W64 x).getLsbD i = x.getLsbD (8 * (7 - i / 8) + i % 8) := by
  simp only [revW]
  interval_cases i <;> simp

theorem revW32_getLsbD (x : BitVec 32) (i : Nat) (hi : i < 32) :
    (revW .W32 x).getLsbD i = x.getLsbD (8 * (3 - i / 8) + i % 8) := by
  simp only [revW]
  interval_cases i <;> simp

/-- **`REV` (64-bit)** reverses the bytes. -/
theorem byteOf_rev64 (x : BitVec 64) {t : Nat} (ht : t < 8) :
    byteOf (UnOp.apply .rev .W64 x) t = byteOf x (7 - t) := by
  apply byteOf_eq_of_getLsbD
  intro j hj
  simp only [UnOp.apply, low_W64, ext_W64]
  rw [revW64_getLsbD _ _ (by omega)]
  congr 1
  omega

/-- **`REV` (32-bit)** reverses the low four bytes. -/
theorem byteOf_rev32 (x : BitVec 64) {t : Nat} (ht : t < 4) :
    byteOf (UnOp.apply .rev .W32 x) t = byteOf x (3 - t) := by
  apply byteOf_eq_of_getLsbD
  intro j hj
  simp only [UnOp.apply, ext_W32, low_W32]
  rw [BitVec.getLsbD_setWidth, revW32_getLsbD _ _ (by omega), BitVec.getLsbD_setWidth,
    show 8 * (3 - (8 * t + j) / 8) + (8 * t + j) % 8 = 8 * (3 - t) + j by omega]
  simp [show 8 * (3 - t) + j < 32 by omega, show 8 * t + j < 64 by omega]

theorem div_mod_256_of_mod {a k N : Nat} (h : 8 * k + 8 ≤ N) :
    a % 2 ^ N / 2 ^ (8 * k) % 256 = a / 2 ^ (8 * k) % 256 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < 8
  · simp [hj, show j + 8 * k < N by omega]
  · simp [hj]

/-- A value's byte `t < 8` is its `u64`'s. -/
theorem byteOf_eq_toUInt64 (x : BitVec 64) {t : Nat} (ht : t < 8) :
    byteOf x t = (UInt64.ofBitVec x >>> (8 * t).toUInt64).toUInt8 := by
  rw [byteOf_mod]
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    UInt64.toNat_ofBitVec, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 256),
    show (8 * t).toUInt64.toNat % 64 = 8 * t by simp; omega]

/-- A value's byte `t < 4` is its `u32`'s. -/
theorem byteOf_eq_toUInt32 (x : BitVec 64) {t : Nat} (ht : t < 4) :
    byteOf x t = ((UInt32.ofNat x.toNat) >>> (8 * t).toUInt32).toUInt8 := by
  rw [byteOf_mod]
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 256),
    Nat.mod_eq_of_lt (show 8 * t < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show 8 * t < 32 by omega), show (2 : Nat) ^ 8 = 256 from rfl]
  exact (div_mod_256_of_mod (N := 32) (by omega)).symm

/-- **An 8-byte store** writes the value's `wordBytes`. -/
theorem bytes_word (x : BitVec 64) :
    (List.range 8).map (byteOf x) = wordBytes (UInt64.ofBitVec x) := by
  unfold wordBytes
  apply List.map_congr_left
  intro t ht
  exact byteOf_eq_toUInt64 x (List.mem_range.mp ht)

/-- **A stored `REV` (32-bit)** is the big-endian bytes of the low word. -/
theorem bytes_rev32 (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .rev .W32 x)) = be32 (UInt32.ofNat x.toNat) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, byteOf_rev32 x (show 0 < 4 by decide), byteOf_rev32 x (show 1 < 4 by decide),
    byteOf_rev32 x (show 2 < 4 by decide), byteOf_rev32 x (show 3 < 4 by decide),
    byteOf_eq_toUInt32 x (show 3 < 4 by decide), byteOf_eq_toUInt32 x (show 2 < 4 by decide),
    byteOf_eq_toUInt32 x (show 1 < 4 by decide), byteOf_eq_toUInt32 x (show 0 < 4 by decide), be32]
  rfl

/-- **A stored `REV` (64-bit)** is the big-endian bytes of the value. -/
theorem bytes_rev64 (x : BitVec 64) :
    (List.range 8).map (byteOf (UnOp.apply .rev .W64 x)) = be64 (UInt64.ofBitVec x) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, byteOf_rev64 x (show 0 < 8 by decide), byteOf_rev64 x (show 1 < 8 by decide),
    byteOf_rev64 x (show 2 < 8 by decide), byteOf_rev64 x (show 3 < 8 by decide),
    byteOf_rev64 x (show 4 < 8 by decide), byteOf_rev64 x (show 5 < 8 by decide),
    byteOf_rev64 x (show 6 < 8 by decide), byteOf_rev64 x (show 7 < 8 by decide),
    byteOf_eq_toUInt64 x (show 0 < 8 by decide), byteOf_eq_toUInt64 x (show 1 < 8 by decide),
    byteOf_eq_toUInt64 x (show 2 < 8 by decide), byteOf_eq_toUInt64 x (show 3 < 8 by decide),
    byteOf_eq_toUInt64 x (show 4 < 8 by decide), byteOf_eq_toUInt64 x (show 5 < 8 by decide),
    byteOf_eq_toUInt64 x (show 6 < 8 by decide), byteOf_eq_toUInt64 x (show 7 < 8 by decide), be64]
  rfl

end

end NativeRustcArm.SphincsVerifyProof
