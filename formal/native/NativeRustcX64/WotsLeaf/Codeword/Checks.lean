module

public import NativeRustcX64.WotsLeaf.Codeword.Exec
public import NativeRustcX64.WotsLeaf.Swar

/-!
# The codeword's tests

The test of `b6` is whether the digest's top 12 bits are set (`b6_cond`), `b7`'s whether it is
not a codeword (`b7_cond`): `b7`'s condition is `cwCond` of the digest's two words, its four
popcounts rustc's (`eval_popLowLo`, `eval_popLowHiN`, `eval_popHighLo`, `eval_popHighHi`) and the
32-bit sum compared with `106` `is_codeword` (`cw_beq`).
-/

namespace NativeRustcX64.WotsLeafProof.Codeword

open NativeRustc NativeRustc.Xmss NativeRustc.Xmss.Swar NativeRustcX64.Sym
open NativeRustcX64.Xmss.WotsLeaf

@[expose] public section

/-- The end of a popcount from per-byte nibble counts `s`. -/
def nibS (s : Sym) : Sym :=
  .bin .shr .W64 (.bin .mul .W64 (.bin .and .W64 (.bin .add .W64 s (.bin .shr .W64 s (.lit 4)))
    (.lit 1085102592571150095)) (.lit 72340172838076673)) (.lit 56)

/-- `(x & m) + ((x >> 2) & m)`. -/
def lowS (x : Sym) (m : Nat) : Sym :=
  .bin .add .W64 (.bin .and .W64 x (.lit m)) (.bin .and .W64 (.bin .shr .W64 x (.lit 2)) (.lit m))

/-- `(m & x) - ((m & x) >> 1)`. -/
def highS (x : Sym) (m : Nat) : Sym :=
  .bin .sub .W64 (.bin .and .W64 (.lit m) x) (.bin .shr .W64 (.bin .and .W64 (.lit m) x) (.lit 1))

/-- `b7`'s condition on the digest's words `lo`, `hi`: the 32-bit sum of the counts is not 106. -/
def cwCond (lo hi : Sym) : SBool :=
  .not (.cmp .eq .W32 (.un .trunc .W32 (.bin .add .W64
    (.bin .add .W32 (nibS (lowS lo 1229782938247303441)) (nibS (lowS hi 300239975158033)))
    (.bin .mul .W64 (.bin .add .W32 (nibS (lowS (highS lo 12297829382473034410) 3689348814741910323))
      (nibS (lowS (highS hi 3002399751580330) 3689348814741910323))) (.lit 2)))) (.lit 106))

end

public section

/-- The top 12 bits of a word are zero when it is below `2 ^ 52`. -/
theorem shr52_eq_zero (x : BitVec 64) : (x >>> 52 = 0#64) ↔ x.toNat < 2 ^ 52 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h'
    rw [Nat.div_eq_zero_iff_lt (by positivity)] at h'
    exact h'
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
    rfl

variable [Labels]

theorem eval_nibS (env : Env) (s : Sym) : (nibS s).eval env = fromNibbles (s.eval env) := by
  simp only [nibS, Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount_lit (show 4 < 64 by decide),
    shiftCount_lit (show 56 < 64 by decide)]
  rfl

theorem eval_lowS (env : Env) (x : Sym) (m : Nat) :
    (lowS x m).eval env = (x.eval env &&& BitVec.ofNat 64 m) +
      ((x.eval env >>> 2) &&& BitVec.ofNat 64 m) := by
  simp only [lowS, Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount_lit (show 2 < 64 by decide)]
  rfl

theorem eval_highS (env : Env) (x : Sym) (m : Nat) :
    (highS x m).eval env = (x.eval env &&& BitVec.ofNat 64 m) -
      ((x.eval env &&& BitVec.ofNat 64 m) >>> 1) := by
  simp only [highS, Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount_lit (show 1 < 64 by decide),
    BitVec.and_comm (BitVec.ofNat 64 m)]
  rfl

theorem eval_popLowLo (env : Env) (x : Sym) :
    (nibS (lowS x 1229782938247303441)).eval env = popLowLo (x.eval env) := by
  rw [eval_nibS, eval_lowS]
  rfl

theorem eval_popLowHiN (env : Env) (x : Sym) :
    (nibS (lowS x 300239975158033)).eval env = popLowHiN (x.eval env) := by
  rw [eval_nibS, eval_lowS]
  rfl

theorem eval_popHighLo (env : Env) (x : Sym) :
    (nibS (lowS (highS x 12297829382473034410) 3689348814741910323)).eval env =
      popHighLo (x.eval env) := by
  rw [eval_nibS, eval_lowS, eval_highS]
  rfl

theorem eval_popHighHi (env : Env) (x : Sym) :
    (nibS (lowS (highS x 3002399751580330) 3689348814741910323)).eval env =
      popHighHi (x.eval env) := by
  rw [eval_nibS, eval_lowS, eval_highS]
  rfl

omit [Labels] in
/-- The 32-bit sum `a + b + 2 (c + d)` compared with `106`, for counts below 64. -/
theorem cw_beq (a b c d : BitVec 64) (ha : a.toNat ≤ 64) (hb : b.toNat ≤ 64) (hc : c.toNat ≤ 64)
    (hd : d.toNat ≤ 64) :
    CmpOp.apply .eq .W32 (UnOp.apply .trunc .W32 (BinOp.apply .add .W64
      (BinOp.apply .add .W32 a b) (BinOp.apply .mul .W64 (BinOp.apply .add .W32 c d)
        (BitVec.ofNat 64 2)))) (BitVec.ofNat 64 106) =
      (a.toNat + b.toNat + 2 * (c.toNat + d.toNat) == 106) := by
  have e : ∀ x y : BitVec 32, (x == y) = (x.toNat == y.toNat) := fun x y ↦ by
    by_cases h : x = y
    · subst h; simp
    · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (fun h' ↦ h (BitVec.eq_of_toNat_eq h'))]
  simp only [CmpOp.apply, UnOp.apply, BinOp.apply, low_W64, ext_W64, low_ext]
  rw [e]
  congr 1
  simp only [toNat_low, toNat_ext, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Width.bits]
  omega

/-- **`b6`'s test**: the digest's top 12 bits set. -/
theorem b6_cond {env : Env} {S : SState} {c : SBool} {l : Label}
    (h : exec b6 (frameS []) = some (S, .cond c l)) {hi : BitVec 64} (hl : env.load 0 120 8 = hi) :
    c.eval env = !decide (hi.toNat < 2 ^ 52) := by
  rw [run_b6] at h
  simp only [Option.some.injEq, Prod.mk.injEq, Exit.cond.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
    shiftCount_lit (show 52 < 64 by decide), hl]
  congr 1
  by_cases h52 : hi.toNat < 2 ^ 52
  · rw [decide_eq_true h52]
    exact beq_iff_eq.mpr ((shr52_eq_zero hi).mpr h52)
  · rw [decide_eq_false h52]
    exact beq_false_of_ne fun h' ↦ h52 ((shr52_eq_zero hi).mp h')

/-- **`b7`'s test**: the digest not a codeword. -/
theorem b7_cond {env : Env} {S : SState} {c : SBool} {l : Label}
    (h : exec b7 s7 = some (S, .cond c l)) {lo hi : BitVec 64}
    (hl : env.load 0 112 8 = lo) (hh : env.load 0 120 8 = hi) (h52 : hi.toNat < 2 ^ 52) :
    c.eval env = !isCodeword (2 ^ 64 * hi.toNat + lo.toNat) := by
  rw [run_b7] at h
  simp only [Option.some.injEq, Prod.mk.injEq, Exit.cond.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  show (cwCond (.load 0 112 8) (.load 0 120 8)).eval env = _
  simp only [cwCond, SBool.eval, Sym.eval, eval_popLowLo, eval_popLowHiN, eval_popHighLo,
    eval_popHighHi, hl, hh]
  rw [isCodeword_swarN lo hi h52]
  have b1 := pop_le (lo.toNat &&& 0x5555555555555555) 64
  have b2 := pop_le (hi.toNat &&& 0x5555555555555555) 64
  have b3 := pop_le (lo.toNat &&& 0xaaaaaaaaaaaaaaaa) 64
  have b4 := pop_le (hi.toNat &&& 0xaaaaaaaaaaaaaaaa) 64
  rw [cw_beq _ _ _ _ (by rw [popLowLo_toNat]; exact b1) (by rw [popLowHiN_toNat hi h52]; exact b2)
    (by rw [popHighLo_toNat]; exact b3) (by rw [popHighHi_toNat hi h52]; exact b4)]

end

end NativeRustcX64.WotsLeafProof.Codeword
