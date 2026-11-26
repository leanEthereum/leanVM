module

public import NativeRustcX64.Sym.Lemmas

/-!
# The codeword's digits as the loop `b104` computes them

The loop (`.LBB2_39`) takes the 128-bit digest `rax : rdx` (high, low) apart into 64 two-bit
digits, the digit at bit `s` (`s` even) the low two bits of `rax >> (s - 64)` when `s ≥ 64`
(`digit_hi`), of `shrd rdx, rax, s` (the low word of `(rax : rdx) >> s`) when `s < 64`
(`digit_lo`), stored as a byte (`movb` of `andb $3`, `byte3`): both are bits `s, s + 1` of
`rax · 2⁶⁴ + rdx`.
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustcX64.Sym

@[expose] public section

/-- A byte register write keeps the written byte. -/
theorem low8_merge (x y : BitVec 64) : low .W8 (BinOp.apply .merge .W8 x y) = low .W8 y := by
  simp only [BinOp.apply, BitVec.replaceLow, BitVec.drop, low, Width.bits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.append_eq, BitVec.getLsbD_append]
  simp [hi, show i < 64 by omega]

/-- **A stored digit**: `andb $3` of a byte register, its byte. -/
theorem byte3 (A : BitVec 64) :
    (UnOp.apply .trunc .W8 (BinOp.apply .merge .W8 A
      (BinOp.apply .and .W8 A (BitVec.ofNat 64 3)))).toNat = A.toNat % 4 := by
  simp only [UnOp.apply]
  rw [toNat_ext, low8_merge, toNat_low]
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, Width.bits, BitVec.toNat_ofNat]
  rw [show (3 : Nat) % 2 ^ 64 % 2 ^ 8 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem two_pow_64_div {X Y : Nat} (hY : Y < 2 ^ 64) : (X * 2 ^ 64 + Y) / 2 ^ 64 = X := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hY,
    Nat.zero_add]

/-- The digit at bit `s ≥ 64`: `rax >> (s - 64)`. -/
theorem digit_hi (x : BitVec 64) {y s : Nat} (hy : y < 2 ^ 64) (hs : 64 ≤ s) (hs' : s < 128) :
    (BinOp.apply .shr .W64 x (BitVec.ofNat 64 s)).toNat % 4 =
      (x.toNat * 2 ^ 64 + y) >>> s % 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = 64 + k := ⟨s - 64, by omega⟩
  have hc : shiftCount .W64 (BitVec.ofNat 64 (64 + k)) = k := by
    simp only [shiftCount, low, Width.bits, shiftMask, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [BinOp.apply, hc, ext_W64, low_W64, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, two_pow_64_div hy]
  simp [Nat.shiftRight_eq_div_pow]

/-- The digit at bit `0 < s < 64`: `shrd`, the low word of `(rax : rdx) >> s`. -/
theorem digit_lo (x y : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) :
    (TernOp.apply .shrd .W64 y x (BitVec.ofNat 64 s)).toNat % 4 =
      (x.toNat * 2 ^ 64 + y.toNat) >>> s % 4 := by
  have hc : shiftCount .W64 (BitVec.ofNat 64 s) = s := by
    simp only [shiftCount, low, Width.bits, shiftMask, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [TernOp.apply, hc, low_W64, ext_W64]
  rw [Sym.ite_neg (by simp; omega)]
  simp only [BitVec.take, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_ushiftRight, BitVec.append_eq, BitVec.toNat_append, Width.bits]
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 64),
    Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64)]

/-- The digit at bit `0`: `shrd` by zero is `rdx`. -/
theorem digit_zero (x y : BitVec 64) :
    (TernOp.apply .shrd .W64 y x (BitVec.ofNat 64 0)).toNat % 4 =
      (x.toNat * 2 ^ 64 + y.toNat) >>> 0 % 4 := by
  simp only [TernOp.apply, shiftCount, low_W64, ext_W64]
  rw [Sym.ite_pos (by decide)]
  simp only [Nat.shiftRight_zero]
  omega

end

end NativeRustcX64.SphincsVerifyProof
