module

public import NativeRustcX64.WotsLeaf.FrameS
public import NativeRustcX64.WotsLeaf.Codeword.Number

/-!
# The digits as the loop computes them

Bits `s, s + 1` of the 128-bit digest `2 ^ 64 hi + lo`: `shrd lo, hi, s` below 64
(`digit_shrd`), `hi >> (s & 63)` above (`digit_shr`); the byte the loop stores, the low byte of
the value merged with its low two bits (`toNat_merge`). The executor's `digitSym d` is digit `d`
(`byteOf_digitSym`).
-/

namespace NativeRustcX64.WotsLeafProof.Codeword

open NativeRustcX64.Sym

@[expose] public section

/-- Digit `d`'s symbolic value: bits `2 d, 2 d + 1` of the 128-bit digest `RDX:RSI`, as the loop
computes them. -/
def digitSym (d : Nat) : Sym :=
  let x : Sym := if 2 * d < 64 then .tern .shrd .W64 (.reg .rsi) (.reg .rdx) (.lit (2 * d))
    else .bin .shr .W64 (.reg .rdx) (.lit (2 * d))
  .un .trunc .W8 (.bin .merge .W8 x (.bin .and .W8 x (.lit 3)))

end

public section

theorem toNat_append' {n k : Nat} (x : BitVec n) (y : BitVec k) :
    (x.append y).toNat = x.toNat <<< k ||| y.toNat := BitVec.toNat_append x y

theorem toNat_ushiftRight' {n : Nat} (x : BitVec n) (k : Nat) :
    (x.ushiftRight k).toNat = x.toNat >>> k := BitVec.toNat_ushiftRight x k

theorem shiftCount_lit {c : Nat} (hc : c < 64) : shiftCount .W64 (BitVec.ofNat 64 c) = c := by
  simp only [shiftCount, shiftMask, toNat_low, BitVec.toNat_ofNat, Width.bits]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  show c &&& (2 ^ 6 - 1) = c
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]

theorem shiftCount_lit64 {c : Nat} (h1 : 64 ≤ c) (hc : c < 128) :
    shiftCount .W64 (BitVec.ofNat 64 c) = c - 64 := by
  simp only [shiftCount, shiftMask, toNat_low, BitVec.toNat_ofNat, Width.bits]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  show c &&& (2 ^ 6 - 1) = c - 64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `shrd lo, hi, s`: the low 64 bits of `hi : lo` shifted right by `s < 64`. -/
theorem digit_shrd (lo hi : BitVec 64) {s : Nat} (hs : s < 64) :
    (TernOp.apply .shrd .W64 lo hi (BitVec.ofNat 64 s)).toNat % 4 =
      (2 ^ 64 * hi.toNat + lo.toNat) >>> s % 4 := by
  simp only [TernOp.apply, shiftCount_lit hs, low_W64, ext_W64]
  split
  · rename_i h0
    have : s = 0 := by simpa using h0
    subst this
    simp only [Nat.shiftRight_zero]
    omega
  · have hl := lo.isLt
    simp only [BitVec.toNat_setWidth, toNat_take', BitVec.toNat_ushiftRight, toNat_append',
      Width.bits, Nat.mod_mod]
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.mul_comm,
      Nat.mod_mod_of_dvd _ (by decide)]

/-- `hi >> (s & 63)` for `64 ≤ s < 128`. -/
theorem digit_shr (lo hi : BitVec 64) {s : Nat} (h1 : 64 ≤ s) (hs : s < 128) :
    (BinOp.apply .shr .W64 hi (BitVec.ofNat 64 s)).toNat % 4 =
      (2 ^ 64 * hi.toNat + lo.toNat) >>> s % 4 := by
  simp only [BinOp.apply, shiftCount_lit64 h1 hs, low_W64, ext_W64, toNat_ushiftRight',
    Nat.shiftRight_eq_div_pow]
  have hl := lo.isLt
  have e : (2 ^ 64 * hi.toNat + lo.toNat) / 2 ^ s = hi.toNat / 2 ^ (s - 64) := by
    rw [show s = 64 + (s - 64) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show (2 ^ 64 * hi.toNat + lo.toNat) / 2 ^ 64 = hi.toNat by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl,
          Nat.zero_add], Nat.add_sub_cancel_left]
  rw [e]

/-- The byte stored: the low byte of `x` merged with `x`'s low two bits. -/
theorem toNat_merge (x : BitVec 64) :
    (UnOp.apply .trunc .W8 (BinOp.apply .merge .W8 x
      (BinOp.apply .and .W8 x (BitVec.ofNat 64 3)))).toNat = x.toNat % 4 := by
  have hy : (low .W8 (ext .W8 (low .W8 x &&& low .W8 (BitVec.ofNat 64 3)))).toNat = x.toNat % 4 := by
    simp only [toNat_low, toNat_ext, BitVec.toNat_and, BitVec.toNat_ofNat, Width.bits]
    rw [show 3 % 2 ^ 64 % 2 ^ 8 = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [UnOp.apply, BinOp.apply, toNat_ext, toNat_low, BitVec.replaceLow,
    BitVec.toNat_setWidth, toNat_append', hy, Width.bits]
  have hlt : x.toNat % 4 < 2 ^ 8 := by omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide)]
  omega

/-- **Digit `d`** of the digest, the byte the loop stores. -/
theorem byteOf_digitSym [Labels] (env : Env) {lo hi : BitVec 64} (hs : env.regs .rsi = lo)
    (hd : env.regs .rdx = hi) {d : Nat} (hd2 : 2 * d < 128) :
    byteOf ((digitSym d).eval env) 0 =
      UInt8.ofNat ((2 ^ 64 * hi.toNat + lo.toNat) >>> (2 * d) &&& 3) := by
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  unfold digitSym
  split
  · rename_i h
    simp only [Sym.eval, hs, hd]
    rw [byteOf, toNat_merge, digit_shrd lo hi h]
    simp
  · rename_i h
    simp only [Sym.eval, hd]
    rw [byteOf, toNat_merge, digit_shr lo hi (by omega) hd2]
    simp

end

end NativeRustcX64.WotsLeafProof.Codeword
