module

public import NativeRustcArm.Sym.Lemmas

/-!
# The codeword's digits as the loop `b110` computes them

The loop (`.LBB2_41`) takes the 128-bit digest `x9 : x10` (high, low) apart into 64 two-bit
digits, the digit at bit `s` (`s` even) as `(x9 >> (s - 64)) & 3` when `s ≥ 64` (`digit_hi`),
else as `(((x9 << 1) << (63 - s)) | (x10 >> s)) & 3` (`digit_lo`, the shifts of AArch64's
`lslv`/`lsrv` taken modulo 64, `63 - s` as `~s`): both are bits `s, s + 1` of `x9 · 2⁶⁴ + x10`.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustcArm.Sym

@[expose] public section

theorem and3_W32 (A : BitVec 64) :
    (BinOp.apply .and .W32 A (BitVec.ofNat 64 3)).toNat = A.toNat % 4 := by
  simp only [BinOp.apply, ext_W32, low_W32, BitVec.toNat_setWidth, BitVec.toNat_and,
    BitVec.toNat_ofNat]
  rw [show (3 : Nat) % 2 ^ 64 % 2 ^ 32 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 2 ∣ 2 ^ 32)]
  omega

theorem two_pow_64_div {X Y : Nat} (hY : Y < 2 ^ 64) : (X * 2 ^ 64 + Y) / 2 ^ 64 = X := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hY,
    Nat.zero_add]

/-- The digit at bit `s ≥ 64`. -/
theorem digit_hi (x9 : BitVec 64) {y s : Nat} (hy : y < 2 ^ 64) (hs : 64 ≤ s) (hs' : s < 128) :
    (BinOp.apply .and .W32 (BinOp.apply .lsrv .W64 x9 (BitVec.ofNat 64 s))
      (BitVec.ofNat 64 3)).toNat = (x9.toNat * 2 ^ 64 + y) >>> s % 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = 64 + k := ⟨s - 64, by omega⟩
  rw [and3_W32]
  simp only [BinOp.apply, ext_W64, low_W64, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show 64 + k < 2 ^ 64 by omega), show (64 + k) % 64 = k by omega,
    Nat.pow_add, ← Nat.div_div_eq_div_mul, two_pow_64_div hy]

theorem ubfm_lsl1 (x : BitVec 64) : UnOp.apply (.ubfm 63 62) .W64 x = x <<< 1 := by
  simp only [UnOp.apply, ext_W64, low_W64]
  unfold evalUBFM BitVec.take
  apply BitVec.eq_of_toNat_eq
  simp [RegWidth.bits, MemWidth.bits, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem lo_nat {X Y s : Nat} (hs : s ≤ 62) :
    (X * 2 ^ 1 % 2 ^ 64 * 2 ^ (63 - s) % 2 ^ 64 % 2 ^ 2 ||| Y / 2 ^ s % 2 ^ 2) =
      (X * 2 ^ 64 + Y) / 2 ^ s % 2 ^ 2 := by
  have h4 : 2 ^ 2 ∣ X * 2 ^ 1 % 2 ^ 64 * 2 ^ (63 - s) % 2 ^ 64 := by
    apply (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by decide : 2 ≤ 64))).2
    have h2 : 2 ∣ X * 2 ^ 1 % 2 ^ 64 :=
      (Nat.dvd_mod_iff (by decide : 2 ∣ 2 ^ 64)).2 (Nat.dvd_mul_left 2 X)
    have h2' : 2 ∣ 2 ^ (63 - s) := Nat.dvd_of_mod_eq_zero (Nat.two_pow_mod_two_eq_zero.2 (by omega))
    exact Nat.mul_dvd_mul h2 h2'
  rw [Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff ?_ |>.2 h4) (Nat.mod_lt _ (by decide)), Nat.zero_or]
  · rw [show X * 2 ^ 64 + Y = Y + X * 2 ^ (64 - s) * 2 ^ s by
        rw [Nat.mul_assoc, ← Nat.pow_add, show 64 - s + s = 64 by omega, Nat.add_comm],
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos s), Nat.add_mod,
      show 2 ^ (64 - s) = 2 ^ 2 * 2 ^ (62 - s) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_left_comm, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  · exact Nat.dvd_refl _

/-- The digit at bit `s ≤ 62`. -/
theorem digit_lo (x9 x10 : BitVec 64) {s : Nat} (hs : s ≤ 62) :
    (BinOp.apply .and .W32 (BinOp.apply .orr .W64 (BinOp.apply .lslv .W64
      (UnOp.apply (.ubfm 63 62) .W64 x9) (BitVec.ofNat 64 (4294967295 - s)))
      (BinOp.apply .lsrv .W64 x10 (BitVec.ofNat 64 s))) (BitVec.ofNat 64 3)).toNat =
      (x9.toNat * 2 ^ 64 + x10.toNat) >>> s % 4 := by
  rw [and3_W32, ubfm_lsl1]
  simp only [BinOp.apply, ext_W64, low_W64, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 4294967295 - s < 2 ^ 64 by omega),
    show (4294967295 - s) % 64 = 63 - s by omega, show s % 64 = s by omega,
    show (4 : Nat) = 2 ^ 2 from rfl, Nat.or_mod_two_pow]
  exact lo_nat hs
end

end NativeRustcArm.SphincsVerifyProof
