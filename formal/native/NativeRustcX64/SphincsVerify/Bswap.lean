module

public import NativeRustcX64.Sym.Simp
public import NativeRustc.Sphincs.Model

/-!
# The bytes of stored values and of `bswap`

A value's low bytes are its `u64`'s or `u32`'s (`byteOf_eq_toUInt64`, `byteOf_eq_toUInt32`): an
8-byte store writes `wordBytes` of it (`bytes_word`). `BSWAP` reverses a value's bytes
(`byteOf_bswap64`, `byteOf_bswap32`): stored, a swapped value is its big-endian bytes
(`bytes_bswap64`, `bytes_bswap32`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustcX64.Sym NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

public section

/-- Two bytes of values are equal when their bits are. -/
theorem byteOf_eq_of_getLsbD {x y : BitVec 64} {t u : Nat}
    (h : ∀ j < 8, x.getLsbD (8 * t + j) = y.getLsbD (8 * u + j)) : byteOf x t = byteOf y u := by
  unfold byteOf
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat']
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and]
    have := h j hj
    rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat] at this
    rwa [Nat.add_comm j, Nat.add_comm j]
  · simp [hj]

theorem bswap64_getLsbD (x : BitVec 64) (i : Nat) (hi : i < 64) :
    (bswap64 x).getLsbD i = x.getLsbD (8 * (7 - i / 8) + i % 8) := by
  simp only [bswap64, BitVec.take, BitVec.drop, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem bswap32_getLsbD (x : BitVec 32) (i : Nat) (hi : i < 32) :
    (bswap32 x).getLsbD i = x.getLsbD (8 * (3 - i / 8) + i % 8) := by
  simp only [bswap32, BitVec.take, BitVec.drop, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- **`BSWAP` (64-bit)** reverses the bytes. -/
theorem byteOf_bswap64 (x : BitVec 64) {t : Nat} (ht : t < 8) :
    byteOf (UnOp.apply .bswap .W64 x) t = byteOf x (7 - t) := by
  apply byteOf_eq_of_getLsbD
  intro j hj
  simp only [UnOp.apply, bswapW, ext, low, Width.bits, BitVec.setWidth_eq]
  rw [bswap64_getLsbD _ _ (by omega)]
  congr 1
  omega

/-- **`BSWAP` (32-bit)** reverses the low four bytes. -/
theorem byteOf_bswap32 (x : BitVec 64) {t : Nat} (ht : t < 4) :
    byteOf (UnOp.apply .bswap .W32 x) t = byteOf x (3 - t) := by
  apply byteOf_eq_of_getLsbD
  intro j hj
  simp only [UnOp.apply, bswapW, ext, low, Width.bits]
  rw [BitVec.getLsbD_setWidth, bswap32_getLsbD _ _ (by omega), BitVec.getLsbD_setWidth,
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
  unfold byteOf
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    UInt64.toNat_ofBitVec, Nat.shiftRight_eq_div_pow]
  rw [show (8 * t).toUInt64.toNat % 64 = 8 * t by simp; omega]

/-- A value's byte `t < 4` is its `u32`'s. -/
theorem byteOf_eq_toUInt32 (x : BitVec 64) {t : Nat} (ht : t < 4) :
    byteOf x t = ((UInt32.ofNat x.toNat) >>> (8 * t).toUInt32).toUInt8 := by
  unfold byteOf
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show 8 * t < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show 8 * t < 32 by omega)]
  exact (div_mod_256_of_mod (N := 32) (by omega)).symm

/-- **An 8-byte store** writes the value's `wordBytes`. -/
theorem bytes_word (x : BitVec 64) :
    (List.range 8).map (byteOf x) = wordBytes (UInt64.ofBitVec x) := by
  unfold wordBytes
  apply List.map_congr_left
  intro t ht
  exact byteOf_eq_toUInt64 x (List.mem_range.mp ht)

/-- **A stored `BSWAP` (32-bit)** is the big-endian bytes of the low word. -/
theorem bytes_bswap32 (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .bswap .W32 x)) = be32 (UInt32.ofNat x.toNat) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, byteOf_bswap32 x (show 0 < 4 by decide),
    byteOf_bswap32 x (show 1 < 4 by decide), byteOf_bswap32 x (show 2 < 4 by decide),
    byteOf_bswap32 x (show 3 < 4 by decide), byteOf_eq_toUInt32 x (show 3 < 4 by decide),
    byteOf_eq_toUInt32 x (show 2 < 4 by decide), byteOf_eq_toUInt32 x (show 1 < 4 by decide),
    byteOf_eq_toUInt32 x (show 0 < 4 by decide), be32]
  rfl

/-- **A stored `BSWAP` (64-bit)** is the big-endian bytes of the value. -/
theorem bytes_bswap64 (x : BitVec 64) :
    (List.range 8).map (byteOf (UnOp.apply .bswap .W64 x)) = be64 (UInt64.ofBitVec x) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, byteOf_bswap64 x (show 0 < 8 by decide),
    byteOf_bswap64 x (show 1 < 8 by decide), byteOf_bswap64 x (show 2 < 8 by decide),
    byteOf_bswap64 x (show 3 < 8 by decide), byteOf_bswap64 x (show 4 < 8 by decide),
    byteOf_bswap64 x (show 5 < 8 by decide), byteOf_bswap64 x (show 6 < 8 by decide),
    byteOf_bswap64 x (show 7 < 8 by decide),
    byteOf_eq_toUInt64 x (show 0 < 8 by decide), byteOf_eq_toUInt64 x (show 1 < 8 by decide),
    byteOf_eq_toUInt64 x (show 2 < 8 by decide), byteOf_eq_toUInt64 x (show 3 < 8 by decide),
    byteOf_eq_toUInt64 x (show 4 < 8 by decide), byteOf_eq_toUInt64 x (show 5 < 8 by decide),
    byteOf_eq_toUInt64 x (show 6 < 8 by decide), byteOf_eq_toUInt64 x (show 7 < 8 by decide), be64]
  rfl

end

end NativeRustcX64.SphincsVerifyProof
