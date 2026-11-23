module

public import NativeRustcArm.WotsLeaf.Codeword.Digits
public import NativeRustcArm.WotsLeaf.Codeword.Swar
public import NativeRustcArm.WotsLeaf.Codeword.Number
public import NativeRustcArm.WotsLeaf.Addr

/-!
# The codeword's tests and values

The test of `b6` is whether the digest's top 12 bits are set (`b6_cond`), `b7`'s whether it is
not a codeword (`b7_cond`); `b8`'s `x11 = (sp + 380) | 1` is the frame's byte 381 (`orr_380`);
`b10`'s digits 56 and 57 (`byte_ubfm48`, `byte_ubfm50`) and `hi >> 16` (`bytes_hi16`).
-/

namespace NativeRustcArm.WotsLeafProof.Codeword

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

public section

/-- The top 12 bits of a word are zero when it is below `2 ^ 52`. -/
theorem and_top_eq_zero (x : BitVec 64) :
    (x &&& 18442240474082181120#64 = 0#64) ↔ x.toNat < 2 ^ 52 := by
  have hm : (18442240474082181120#64).toNat = (2 ^ 12 - 1) * 2 ^ 52 := rfl
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, hm] at h'
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hi64 : i < 64
    · have := congrArg (·.testBit i) h'
      simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
        BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_testBit] at this
      simpa [hi, show i - 52 < 12 by omega] using this
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hm]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.zero_testBit]
    by_cases hi : 52 ≤ i
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))]
      simp
    · simp [hi]

variable [Labels]

/-- **`b6`'s test**: the digest's top 12 bits set. -/
theorem b6_cond {env : Env} {S : SState} {c : SBool} {l : Label}
    (h : exec b6 (frameS []) = some (S, .cond c l)) {hi : BitVec 64} (hl : env.load 0 1784 8 = hi) :
    c.eval env = !decide (hi.toNat < 2 ^ 52) := by
  rw [run_b6] at h
  simp only [Option.some.injEq, Prod.mk.injEq, Exit.cond.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  sym_simp
  rw [hl]
  congr 1
  by_cases h52 : hi.toNat < 2 ^ 52
  · rw [decide_eq_true h52, beq_iff_eq.mpr ((and_top_eq_zero hi).mpr h52)]
  · rw [decide_eq_false h52]
    exact beq_false_of_ne fun h' ↦ h52 ((and_top_eq_zero hi).mp h')

/-- **`b7`'s test**: the digest not a codeword. -/
theorem b7_cond {env : Env} {S : SState} {c : SBool} {l : Label}
    (h : exec b7 (frameS []) = some (S, .cond c l)) {lo hi : BitVec 64}
    (hl : env.load 0 1776 8 = lo) (h8 : env.regs .X8 = hi) (h52 : hi.toNat < 2 ^ 52) :
    c.eval env = !isCodeword (2 ^ 64 * hi.toNat + lo.toNat) := by
  rw [run_b7] at h
  simp only [Option.some.injEq, Prod.mk.injEq, Exit.cond.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  sym_simp
  simp only [evalUBFM_2, evalUBFM_56]
  rw [hl, h8, ← swar_beq lo hi h52]
  rfl

omit [Labels] in
/-- `(sp + 380) | 1` with SP 16-byte aligned. -/
theorem orr_380 {b : BitVec 64} (hb : b.toNat % 16 = 0) (hn : b.toNat + 381 < 2 ^ 64) :
    (b + BitVec.ofInt 64 380) ||| BitVec.ofNat 64 1 = b + BitVec.ofNat 64 381 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, show BitVec.ofInt 64 380 = BitVec.ofNat 64 380 from rfl,
    toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.or_comm, lor_eq_add (n := 1) (by decide) (by omega)]
  omega

omit [Labels] in
/-- **Digit 56**, `ubfx x9, x8, #48, #2`. -/
theorem byte_ubfm48 (lo hi : BitVec 64) :
    byteOf (UnOp.apply (.ubfm 48 49) .W64 hi) 0 =
      UInt8.ofNat ((2 ^ 64 * hi.toNat + lo.toNat) >>> (2 * 56) &&& 3) := by
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← digit_hi lo hi (s := 2 * 56) (by omega)]
  simp only [byteOf, UnOp.apply, evalUBFM, Sym.ext, Sym.low, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  apply UInt8.toNat_inj.mp
  simp [toNat_take'', Nat.mod_eq_of_lt hi.isLt]

omit [Labels] in
/-- **Digit 57**, `lsr x8, x8, #50`, with the top 12 bits zero. -/
theorem byte_ubfm50 (lo hi : BitVec 64) (h52 : hi.toNat < 2 ^ 52) :
    byteOf (UnOp.apply (.ubfm 50 63) .W64 hi) 0 =
      UInt8.ofNat ((2 ^ 64 * hi.toNat + lo.toNat) >>> (2 * 57) &&& 3) := by
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← digit_hi lo hi (s := 2 * 57) (by omega)]
  have e : UnOp.apply (.ubfm 50 63) .W64 hi = hi >>> 50 := by
    simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
    exact evalUBFM_lsr hi (by decide)
  rw [e]
  simp only [byteOf, Nat.mul_zero, Nat.pow_zero, Nat.div_one, show 2 * 57 - 64 = 50 from rfl]
  have : (hi >>> 50).toNat < 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [Nat.mod_eq_of_lt this]

/-- **`hi >> 16`**'s four bytes, `lsr w8, w8, #16` of the loaded `hi`. -/
theorem bytes_hi16 {env : Env} {h : UInt32}
    (hl : env.load 0 28 4 = BitVec.ofInt 64 (Int.ofBytes (u32Bytes h))) :
    (List.range 4).map (byteOf ((Sym.un (.ubfm 16 31) .W32 (.load 0 28 4)).eval env)) =
      u32Bytes (h >>> 16) := by
  have hv : (env.load 0 28 4).toNat = h.toNat := by
    rw [hl, toNat_ofInt_ofBytes' (by rw [length_u32Bytes]; decide), u32Bytes, leNat_bytes]
    exact Nat.mod_eq_of_lt (by have := h.toNat_lt; simpa using this)
  have he : ((Sym.un (.ubfm 16 31) .W32 (.load 0 28 4)).eval env).toNat = h.toNat >>> 16 := by
    show (UnOp.apply (.ubfm 16 31) .W32 (env.load 0 28 4)).toNat = _
    simp only [UnOp.apply, evalUBFM, Sym.ext_W32, Sym.low, RegWidth.bits]
    simp [toNat_take'', BitVec.toNat_ushiftRight, hv, Nat.shiftRight_eq_div_pow]
    have := h.toNat_lt
    omega
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.cons.injEq, and_true]
  have hs : (h >>> 16).toNat = h.toNat >>> 16 := by
    simp [UInt32.toNat_shiftRight]
  refine ⟨u8_ext ?_, u8_ext ?_, u8_ext ?_, u8_ext ?_⟩ <;>
    simp [byteOf_toNat, he, hs, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

end

end NativeRustcArm.WotsLeafProof.Codeword
