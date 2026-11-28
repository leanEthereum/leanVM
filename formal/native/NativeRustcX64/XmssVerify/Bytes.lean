module

public import NativeRustcX64.XmssVerify.Model
public import NativeRustcX64.XmssVerify.Calls

/-!
# `xmss_verify`: the values its path loops compute (x86-64)

The test of bit `z` of the key index in RBX (`bitC`, `bitC_eval`), a node address's low field
(`loW`, `loW_toNat`), the bytes of a 32-bit store (`u32Bytes_byteOf`) and of a 64-bit load
(`regBytes_load`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym NativeRustc

@[expose] public section

/-- `(1 << z) & EBX == 0`, `z` the low 32 bits of `zs`. -/
def bitC (zs : Sym) : SBool :=
  .cmp .eq .W32 (.bin .and .W32 (.bin .shl .W64 (.lit 1) (.un .trunc .W32 zs)) (.reg .rbx)) (.lit 0)

/-- `RBX >> z`'s low 32 bits, `z` the low 32 bits of `zs`. -/
def loW (zs : Sym) : Sym := .un .trunc .W32 (.bin .shr .W64 (.reg .rbx) (.un .trunc .W32 zs))

end

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

variable [Labels] {env : Env}

theorem shiftCount_trunc {zs : Sym} {z : Nat} (hz : zs.eval env = BitVec.ofNat 64 z)
    (hz32 : z < 32) (w : Width) :
    shiftCount w ((Sym.un .trunc .W32 zs).eval env) = z := by
  have hm : z &&& shiftMask w = z := by
    have : z &&& 31 = z := by
      rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    cases w <;> simp only [shiftMask] <;> first | exact this |
      (rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega)
  simp only [shiftCount, Sym.eval, UnOp.apply, low, ext, hz, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [show Width.W32.bits = 32 from rfl, show Width.W8.bits = 8 from rfl]
  rw [Nat.mod_eq_of_lt (show z < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show z < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show z < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show z < 2 ^ 8 by omega), hm]

omit [Labels] in
theorem beq_zero (X : BitVec 32) : (X == low .W32 (BitVec.ofNat 64 0)) = decide (X.toNat = 0) := by
  by_cases h : X.toNat = 0
  · rw [decide_eq_true h, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    exact h (by rw [h']; rfl)

set_option linter.unusedSimpArgs false in
/-- **The test of bit `z`** of the key index `e` in RBX. -/
theorem bitC_eval {zs : Sym} {z e : Nat} (hz : zs.eval env = BitVec.ofNat 64 z) (hz32 : z < 32)
    (hbx : env.regs .rbx = BitVec.ofNat 64 e) (he : e < 2 ^ 32) :
    (bitC zs).eval env = decide (e >>> z &&& 1 = 0) := by
  have hs : shiftCount .W64 (UnOp.apply .trunc .W32 (zs.eval env)) = z :=
    shiftCount_trunc hz hz32 .W64
  simp only [bitC, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply]
  rw [hs, hbx, beq_zero]
  refine decide_eq_decide.mpr ?_
  rw [← two_pow_and_eq_zero]
  have h2 : 2 ^ z < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hz32
  have hl : 2 ^ z &&& e < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left h2
  have f1 : 1 % 2 ^ 64 = 1 := rfl
  have f2 : 2 ^ z % 2 ^ 64 = 2 ^ z := Nat.mod_eq_of_lt (by omega)
  have f3 : 2 ^ z % 2 ^ 32 = 2 ^ z := Nat.mod_eq_of_lt h2
  have f4 : e % 2 ^ 64 = e := Nat.mod_eq_of_lt (by omega)
  have f5 : e % 2 ^ 32 = e := Nat.mod_eq_of_lt he
  have f6 : (2 ^ z &&& e) % 2 ^ 64 = 2 ^ z &&& e := Nat.mod_eq_of_lt (by omega)
  have f7 : (2 ^ z &&& e) % 2 ^ 32 = 2 ^ z &&& e := Nat.mod_eq_of_lt hl
  simp only [low, ext, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, show Width.W32.bits = 32 from rfl, show Width.W64.bits = 64 from rfl,
    Nat.shiftLeft_eq, Nat.one_mul, f1, f2, f3, f4, f5, f6, f7]

set_option linter.unusedSimpArgs false in
/-- **A node address's low field**: the key index `e` in RBX shifted by `z`. -/
theorem loW_toNat {zs : Sym} {z e : Nat} (hz : zs.eval env = BitVec.ofNat 64 z) (hz32 : z < 32)
    (hbx : env.regs .rbx = BitVec.ofNat 64 e) (he : e < 2 ^ 32) :
    ((loW zs).eval env).toNat = e >>> z := by
  have hs : shiftCount .W64 (UnOp.apply .trunc .W32 (zs.eval env)) = z :=
    shiftCount_trunc hz hz32 .W64
  have hs' : shiftCount .W64 (ext .W32 (low .W32 (zs.eval env))) = z := hs
  simp only [loW, Sym.eval, UnOp.apply, BinOp.apply]
  rw [hs', hbx]
  have : e >>> z ≤ e := Nat.shiftRight_le e z
  have f4 : e % 2 ^ 64 = e := Nat.mod_eq_of_lt (by omega)
  have f2 : e >>> z % 2 ^ 32 = e >>> z := Nat.mod_eq_of_lt (by omega)
  have f3 : e >>> z % 2 ^ 64 = e >>> z := Nat.mod_eq_of_lt (by omega)
  simp only [low, ext, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    show Width.W32.bits = 32 from rfl, show Width.W64.bits = 64 from rfl, f2, f3, f4]
  have e1 : ((BitVec.setWidth Width.W64.bits (BitVec.ofNat 64 e)).ushiftRight z).toNat =
      e >>> z := by
    show (BitVec.setWidth 64 (BitVec.ofNat 64 e) >>> z).toNat = _
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [f4, f4]
  rw [e1, f3, f2, f3]

omit [Labels] in
theorem byteOf_toNat (x : BitVec 64) (t : Nat) :
    (byteOf x t).toNat = x.toNat / 2 ^ (8 * t) % 256 := by
  simp [byteOf]

omit [Labels] in
/-- **A 32-bit store's bytes**: those of the value's `u32`. -/
theorem u32Bytes_byteOf (x : BitVec 64) {n : Nat} (h : x.toNat = n) :
    (List.range 4).map (byteOf x) = u32Bytes n.toUInt32 := by
  subst h
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.cons.injEq, and_true]
  refine ⟨UInt8.toNat_inj.mp ?_, UInt8.toNat_inj.mp ?_, UInt8.toNat_inj.mp ?_,
    UInt8.toNat_inj.mp ?_⟩ <;> simp [byteOf_toNat] <;> omega

omit [Labels] in
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

end NativeRustcX64.Xmss.XmssVerify
