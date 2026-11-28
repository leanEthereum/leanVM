module

public import NativeRustcArm.XmssVerify.Frame

/-!
# `xmss_verify`: the values its loop blocks compute

The test of a key index's bit `z` (`tst (1 << z), e`, `bit_eq`), `lsr w, w, #16` (`ubfm16_toNat`),
the bytes of a 32-bit store (`u32Bytes_byteOf`), of a 64-bit load (`regBytes_load`), and pieces of
known bytes (`BytesAt.take`, `BytesAt.drop`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustc

public section

theorem two_pow_and_eq_zero (x z : Nat) : 2 ^ z &&& x = 0 ↔ x >>> z &&& 1 = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  constructor
  · intro h
    have : (2 ^ z &&& x).testBit z = (0 : Nat).testBit z := by rw [h]
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Nat.zero_testBit, Bool.true_and,
      Nat.testBit_eq_decide_div_mod_eq] at this
    simp only [decide_eq_false_iff_not] at this
    omega
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : z = i
    · subst hi
      simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hi]

/-- **The test of bit `z`** of `E`: `(1 << z) & E == 0`. -/
theorem bit_eq (E : BitVec 64) (z : Nat) (hz : z < 64) :
    ((1#64 <<< z) &&& E == 0#64) = decide (E.toNat >>> z &&& 1 = 0) := by
  have h2 : (1#64 <<< z).toNat = 2 ^ z := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.one_mod_two_pow (by omega), Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hz)
  have key : (1#64 <<< z) &&& E = 0#64 ↔ E.toNat >>> z &&& 1 = 0 := by
    rw [← two_pow_and_eq_zero, ← h2, ← BitVec.toNat_and]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  by_cases h : (1#64 <<< z) &&& E = 0#64
  · rw [decide_eq_true (key.mp h), h]
    rfl
  · rw [decide_eq_false (mt key.mpr h)]
    exact beq_eq_false_iff_ne.mpr h

theorem toNat_take {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsr w, w, #16`. -/
theorem ubfm16_toNat (x : BitVec 64) :
    (UnOp.apply (.ubfm 16 31) .W32 x).toNat = x.toNat % 2 ^ 32 / 2 ^ 16 := by
  simp [UnOp.apply, evalUBFM, Sym.ext_W32, Sym.low, RegWidth.bits, toNat_take]
  omega

theorem byteOf_toNat (x : BitVec 64) (t : Nat) :
    (byteOf x t).toNat = x.toNat / 2 ^ (8 * t) % 256 := by
  simp [byteOf]

theorem u8_ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.toNat_inj.mp h

/-- **A 32-bit store's bytes**: those of the value's `u32`. -/
theorem u32Bytes_byteOf (x : BitVec 64) {n : Nat} (h : x.toNat = n) :
    (List.range 4).map (byteOf x) = u32Bytes n.toUInt32 := by
  subst h
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.cons.injEq, and_true]
  refine ⟨u8_ext ?_, u8_ext ?_, u8_ext ?_, u8_ext ?_⟩ <;> simp [byteOf_toNat] <;> omega

theorem _root_.NativeRustcArm.BytesAt.take {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs)
    (n : Nat) : BytesAt d a (bs.take n) := by
  rw [← List.take_append_drop n bs] at h
  exact h.left

theorem _root_.NativeRustcArm.BytesAt.drop {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs)
    {n : Nat} (hn : n ≤ bs.length) : BytesAt d (a + BitVec.ofNat 64 n) (bs.drop n) := by
  rw [← List.take_append_drop n bs] at h
  have := h.right
  rwa [List.length_take, Nat.min_eq_left hn] at this

variable {env : Env}

/-- **A 64-bit load's bytes** are the bytes it loads. -/
theorem regBytes_load {r off : Nat} {bs : List UInt8} (hl : bs.length = 8)
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) bs) :
    regBytes (env.load r off 8) = bs := by
  apply List.ext_getElem (by rw [length_regBytes, hl])
  intro i h1 h2
  rw [length_regBytes] at h1
  simp only [regBytes, List.getElem_map, List.getElem_range]
  rw [byteOf_load h1 (le_refl 8), ← addr_add_addr, h i h2]
  rfl

end

end NativeRustcArm.Xmss.XmssVerify
