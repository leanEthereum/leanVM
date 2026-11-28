module

public import NativeRustcArm.Sym.Simp
public import NativeRustc.Sphincs.Model
import Mathlib.Tactic.IntervalCases

/-!
# The digest's bit loop, bit by bit

`digest_fields`' leaf `c` is ten bits of `h_msg` from bit `10 c`, most significant first. Turn
`c` of the loop `b57` (X8 `10 c`, X21 `h_msg`) computes bit `10 c + j` as `t<j>`: the byte
`(X8 + j) >> 3` shifted right by `7 - (X8 + j) % 8` (the shift computed from `X8 & 6`, X8 even);
its bit 0 is the bit (`t_eval`). The leaf assembles the ten bits at fixed places (`comb`,
`comb_eval`: `bitsVal` of the bits' low bits). So the leaf is `digest_fields`' (`comb_leaf`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

/-- `[Xn, Xm]`: the index register unextended. -/
abbrev ux0 : MemExtend := { type := MemExtendType.UXTX, amount := MemExtendAmount.E0 }

/-- Bit `X8 + 0` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t0 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.reg (.X8)))) 1) (.bin (.eor) (.W64) (.bin (.and) (.W64) (.reg (.X8)) (.lit 6)) (.lit 7)))

/-- Bit `X8 + 1` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t1 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.reg (.X8)))) 1) (.bin (.eor) (.W32) (.bin (.and) (.W64) (.reg (.X8)) (.lit 6)) (.lit 6)))

/-- Bit `X8 + 2` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t2 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 2)))) 1) (.bin (.eor) (.W32) (.bin (.and) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 2)) (.lit 6)) (.lit 7)))

/-- Bit `X8 + 3` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t3 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 3)))) 1) (.bin (.bic) (.W32) (.lit 6) (.un (.trunc) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 3)))))

/-- Bit `X8 + 4` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t4 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 4)))) 1) (.bin (.eor) (.W32) (.bin (.and) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 4)) (.lit 6)) (.lit 7)))

/-- Bit `X8 + 5` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t5 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 5)))) 1) (.bin (.bic) (.W32) (.lit 6) (.un (.trunc) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 5)))))

/-- Bit `X8 + 6` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t6 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 6)))) 1) (.bin (.eor) (.W32) (.bin (.and) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 6)) (.lit 6)) (.lit 7)))

/-- Bit `X8 + 7` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t7 : Sym :=
  (.bin (.lsrv) (.W32) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 7)))) 1) (.bin (.bic) (.W32) (.lit 6) (.un (.trunc) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 7)))))

/-- Bit `X8 + 8` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t8 : Sym :=
  (.bin (.lsrv) (.W64) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 8)))) 1) (.bin (.eor) (.W64) (.bin (.and) (.W64) (.reg (.X8)) (.lit 6)) (.lit 7)))

/-- Bit `X8 + 9` of `h_msg`, shifted down to bit 0 (`lsr`). -/
def t9 : Sym :=
  (.bin (.lsrv) (.W64) (.loadx 0 0 (.un (.memExtend ux0) (.W64) (.un (.ubfm 3 63) (.W64) (.bin (.add) (.W64) (.reg (.X8)) (.lit 9)))) 1) (.bin (.and) (.W64) (.bin (.orn) (.W32) (.lit 0) (.un (.trunc) (.W32) (.bin (.add) (.W64) (.reg (.X8)) (.lit 9)))) (.lit 6)))

/-- The leaf from its ten bits: `bfi`, `ubfiz`, `bfxil`, `orr` at fixed places. -/
def comb (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Sym) : Sym :=
  (.bin (.orr) (.W64) (.bin (.and) (.W64) t9 (.lit 1)) (.un (.shift (.LSL) 1) (.W64) (.bin (.bfm 0 0) (.W64) (.bin (.orr) (.W64) (.bin (.and) (.W64) (.bin (.orr) (.W32) (.un (.ubfm 30 0) (.W32) t6) (.un (.shift (.LSL) 3) (.W32) (.bin (.bfm 0 0) (.W32) (.bin (.orr) (.W32) (.un (.ubfm 31 0) (.W32) t4) (.un (.shift (.LSL) 2) (.W32) (.bin (.bfm 0 0) (.W32) (.bin (.orr) (.W32) (.un (.ubfm 31 0) (.W32) t2) (.un (.shift (.LSL) 2) (.W32) (.bin (.bfm 31 0) (.W32) (.bin (.and) (.W32) t1 (.lit 1)) t0))) t3))) t5))) (.lit 1020)) (.un (.ubfm 31 0) (.W32) t7)) t8)))
/-- Ten bits, most significant first. -/
def bitsVal (b : Nat → BitVec 64) : BitVec 64 := (List.range 10).foldl (fun v j ↦ v <<< 1 ||| b j) 0

/-- The `j`th bit's value. -/
def T (j : Nat) : Sym := [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9].getD j (.lit 0)

end

public section

/-- **The leaf from its bits**: `comb` of ten values is `bitsVal` of their low bits. -/
theorem comb_eval [Labels] (env : Env) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Sym) :
    (comb a0 a1 a2 a3 a4 a5 a6 a7 a8 a9).eval env = bitsVal fun j ↦
      ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].getD j (.lit 0)).eval env &&& 1 := by
  simp only [comb, bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  sym_simp
  generalize a0.eval env = v0
  generalize a1.eval env = v1
  generalize a2.eval env = v2
  generalize a3.eval env = v3
  generalize a4.eval env = v4
  generalize a5.eval env = v5
  generalize a6.eval env = v6
  generalize a7.eval env = v7
  generalize a8.eval env = v8
  generalize a9.eval env = v9
  simp only [evalBFM, evalUBFM, maskOfLen, BitVec.take, RegWidth.bits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [MemWidth.bits] at hi
  simp
  interval_cases i <;> simp

theorem lsrv_bit_W32 {L : BitVec 64} {x : UInt8} (hL : L = BitVec.ofNat 64 x.toNat) (s : Nat) :
    BitVec.setWidth 64 ((BitVec.setWidth 32 L).ushiftRight (s % 32)) &&& 1 =
      BitVec.ofNat 64 (x.toNat / 2 ^ (s % 32) % 2) := by
  subst hL
  have hx := x.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ushiftRight_eq, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hq : x.toNat / 2 ^ (s % 32) ≤ x.toNat := Nat.div_le_self _ _
  simp only [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show x.toNat / 2 ^ (s % 32) < 2 ^ 64 by omega)]
  have : x.toNat / 2 ^ (s % 32) % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem lsrv_bit_W64 {L : BitVec 64} {x : UInt8} (hL : L = BitVec.ofNat 64 x.toNat) (s : Nat) :
    L.ushiftRight (s % 64) &&& 1 = BitVec.ofNat 64 (x.toNat / 2 ^ (s % 64) % 2) := by
  subst hL
  have hx := x.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ushiftRight_eq, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have h1 : x.toNat % 2 ^ 64 = x.toNat := by omega
  rw [h1]
  have : x.toNat / 2 ^ (s % 64) % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

/-- **Bit `10 c + j` of `h_msg`** (the bytes `h` region 0 holds), turn `c` of the loop. -/
theorem t_eval [Labels] (env : Env) (h : List UInt8) {c : Nat} (hc : c < 24) {j : Nat} (hj : j < 10)
    (hx : env.regs .X8 = BitVec.ofNat 64 (10 * c))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.ofNat 64 (h.getD k 0).toNat) :
    (T j).eval env &&& 1 =
      BitVec.ofNat 64 ((h.getD ((10 * c + j) / 8) 0).toNat / 2 ^ (7 - (10 * c + j) % 8) % 2) := by
  interval_cases j <;>
  · simp only [T, List.getD_cons_zero, List.getD_cons_succ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]
    sym_simp
    rw [hx, RegWidth.bits]
    first
    | rw [lsrv_bit_W32 (hb _ (by clear hx hb; revert c; decide))]
    | rw [lsrv_bit_W64 (hb _ (by clear hx hb; revert c; decide))]
    congr 4
    · congr 1; clear hx hb; revert c; decide
    · clear hx hb; revert c; decide

/-- `digest_fields`' bit, by division. -/
theorem digestBit_eq (d : List UInt8) (p : Nat) :
    digestBit d p = (d.getD (p / 8) 0).toNat / 2 ^ (7 - p % 8) % 2 := by
  have hs : (7 - p % 8) < 8 := by omega
  simp only [digestBit, UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (1 : UInt8).toNat = 1 from rfl, Nat.and_one_is_mod]
  congr 3
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ofNat_shiftLeft_one (v : Nat) :
    BitVec.ofNat 64 (v <<< 1) = BitVec.ofNat 64 v <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `bitsVal` of bits given as numbers is the number they make. -/
theorem ofNat_bitsVal (f : Nat → Nat) :
    BitVec.ofNat 64 ((List.range 10).foldl (fun v j ↦ v <<< 1 ||| f j) 0) =
      bitsVal fun j ↦ BitVec.ofNat 64 (f j) := by
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.ofNat_or, ofNat_shiftLeft_one]
  rfl

theorem bitsVal_congr {b b' : Nat → BitVec 64} (h : ∀ j < 10, b j = b' j) : bitsVal b = bitsVal b' := by
  unfold bitsVal
  exact List.foldl_ext _ _ _ fun v j hj ↦ by rw [h j (List.mem_range.mp hj)]

/-- **Turn `c` of the loop computes leaf `c`** of `digest_fields` of `h`, the bytes region 0
holds. -/
theorem comb_leaf [Labels] (env : Env) (h : List UInt8) {c : Nat} (hc : c < 24)
    (hx : env.regs .X8 = BitVec.ofNat 64 (10 * c))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.ofNat 64 (h.getD k 0).toNat) :
    (comb t0 t1 t2 t3 t4 t5 t6 t7 t8 t9).eval env =
      BitVec.ofNat 64 ((List.range 10).foldl (fun v j ↦ v <<< 1 ||| digestBit h (10 * c + j)) 0) := by
  rw [comb_eval, ofNat_bitsVal]
  apply bitsVal_congr
  intro j hj
  rw [digestBit_eq]
  exact t_eval env h hc hj hx hb

end

end NativeRustcArm.SphincsVerifyProof.Digest
