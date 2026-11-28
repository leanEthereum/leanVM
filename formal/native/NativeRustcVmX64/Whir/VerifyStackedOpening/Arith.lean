module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Whir.VerifyStackedOpening.Exec

/-!
# `verify_stacked_opening`: the values its blocks compute (x86-64)

The comparisons with `157` (`ja`/`jbe` on a column), the `present` bit `setne` leaves
(`eval_bit`), the placement's index `24 c` (`toNat_idx`), the equality `je` tests
(`eval_eq64`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym

public section

theorem u64n {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem u64_bv0 (w : UInt64) : (w.toBitVec = 0#64) ↔ w = 0 := by
  constructor
  · intro h; exact UInt64.toBitVec_inj.mp (h.trans rfl)
  · intro h; rw [h]; rfl

theorem toNat_add_small {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

variable [Labels] {env : Env}

theorem eval_add64 (x y : Sym) : (Sym.bin .add .W64 x y).eval env = x.eval env + y.eval env := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

/-- `ja` after `cmp $157`: above `157`. -/
theorem eval_gt157 (X : Sym) :
    (SBool.and (.not (.cmp .ult .W64 X (.lit 157))) (.not (.cmp .eq .W64 X (.lit 157)))).eval env =
      decide (157 < (X.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  generalize X.eval env = x
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, BitVec.ult, beq_eq_false_iff_ne,
    ne_eq, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt]
  rw [BitVec.toNat_ofNat, show (157 : Nat) % 2 ^ Width.W64.bits = 157 from rfl]
  constructor
  · rintro ⟨h1, h2⟩
    have : x.toNat ≠ 157 := fun h ↦ h2 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    omega
  · intro h
    exact ⟨by omega, fun he ↦ by rw [he] at h; simp at h⟩

/-- `jbe` after `cmp $157`: at most `157`. -/
theorem eval_le157 (X : Sym) :
    (SBool.or (.cmp .ult .W64 X (.lit 157)) (.cmp .eq .W64 X (.lit 157))).eval env =
      decide ((X.eval env).toNat ≤ 157) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  generalize X.eval env = x
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, BitVec.ult, decide_eq_true_eq, beq_iff_eq]
  rw [BitVec.toNat_ofNat, show (157 : Nat) % 2 ^ Width.W64.bits = 157 from rfl]
  constructor
  · rintro (h | h)
    · omega
    · rw [h]; decide
  · intro h
    by_cases he : x.toNat = 157
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [he]; rfl))
    · exact .inl (by omega)

/-- `setne` into a cleared register: the bit of a nonzero value. -/
theorem eval_bit (Y : Sym) :
    (Sym.bin .merge .W8 (.lit 0) (.ite (.not (.cmp .eq .W64 Y (.lit 0))) (.lit 1) (.lit 0))).eval
      env = BitVec.ofNat 64 (if Y.eval env = 0#64 then 0 else 1) := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, BinOp.apply]
  generalize Y.eval env = y
  by_cases hy : y = 0#64
  · subst hy; decide
  · have : (y == BitVec.ofNat 64 0) = false := by
      rw [beq_eq_false_iff_ne]; exact hy
    simp only [this, Bool.not_false, ↓reduceIte, hy]
    decide

/-- Three times a value, as `leaq (%x,%x,2)` computes it. -/
theorem toNat_t3 (X : Sym) (h : (X.eval env).toNat < 2 ^ 62) :
    ((t3 X).eval env).toNat = 3 * (X.eval env).toNat := by
  simp only [t3, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofNat]
  omega

/-- A placement's word index, scaled. -/
theorem toNat_idx (X : Sym) (h : (X.eval env).toNat < 2 ^ 58) :
    ((Sym.bin .mul .W64 (t3 X) (.lit 8)).eval env).toNat = 24 * (X.eval env).toNat := by
  have h3 := toNat_t3 (env := env) X (by omega)
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat] at h3 ⊢
  rw [h3]
  omega

/-- `je` after `cmp` of two registers. -/
theorem eval_eq64 (X Y : Sym) :
    (SBool.cmp .eq .W64 X Y).eval env = decide ((X.eval env).toNat = (Y.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_inj]

/-- A conditional move on `x < c` (`cmovb`), taken. -/
theorem eval_ite_ult (X A B : Sym) {c : Nat} (h : (X.eval env).toNat < c) (hc : c < 2 ^ 64) :
    (Sym.ite (.cmp .ult .W64 X (.lit c)) A B).eval env = A.eval env := by
  have : (X.eval env).ult (BitVec.ofNat 64 c) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hc]; exact h
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, this, ↓reduceIte]

/-- A conditional move on `x ≥ c` (`cmovae`, `not (x < c)`), not taken. -/
theorem eval_ite_not_ult (X A B : Sym) {c : Nat} (h : (X.eval env).toNat < c) (hc : c < 2 ^ 64) :
    (Sym.ite (.not (.cmp .ult .W64 X (.lit c))) A B).eval env = B.eval env := by
  have : (X.eval env).ult (BitVec.ofNat 64 c) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hc]; exact h
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, this, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]

/-- `test %x, %x; je`: zero. -/
theorem eval_test0 (X : Sym) :
    (SBool.cmp .eq .W64 (.bin .and .W64 X X) (.lit 0)).eval env = decide ((X.eval env).toNat = 0) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, BinOp.apply, ext_W64, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp

/-- `cmp $c, %x; jne`. -/
theorem eval_ne_lit (X : Sym) {c : Nat} (hc : c < 2 ^ 64) :
    (SBool.not (.cmp .eq .W64 X (.lit c))).eval env = !decide ((X.eval env).toNat = c) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc]

/-- `ja` after `cmp $c`: above `c`. -/
theorem eval_gt (X : Sym) {c : Nat} (hc : c < 2 ^ 64) :
    (SBool.and (.not (.cmp .ult .W64 X (.lit c))) (.not (.cmp .eq .W64 X (.lit c)))).eval env =
      decide (c < (X.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  generalize X.eval env = x
  have e : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, BitVec.ult,
    beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt, e]
  constructor
  · rintro ⟨h1, h2⟩
    have : x.toNat ≠ c := fun h' ↦ h2 (BitVec.eq_of_toNat_eq (by rw [h', e]))
    omega
  · intro h'
    exact ⟨by omega, fun he ↦ by rw [he, e] at h'; omega⟩

/-- `testb $1, %x; je`: even. -/
theorem eval_even (X : Sym) :
    (SBool.cmp .eq .W8 (.bin .and .W8 X (.lit 1)) (.lit 0)).eval env =
      decide ((X.eval env).toNat % 2 = 0) := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_ext]
  generalize X.eval env = x
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_and,
    toNat_low, toNat_low, toNat_low]
  have h1 : (BitVec.ofNat 64 1).toNat % 2 ^ Width.W8.bits = 1 := rfl
  have h0 : (BitVec.ofNat 64 0).toNat % 2 ^ Width.W8.bits = 0 := rfl
  rw [h1, h0, Nat.and_one_is_mod, show 2 ^ Width.W8.bits = 256 from rfl]
  omega

theorem eval_xor64 (x y : Sym) : (Sym.bin .xor .W64 x y).eval env = x.eval env ^^^ y.eval env := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

/-- `shl $j`. -/
theorem eval_shl_lit' (x : Sym) {j : Nat} (hj : j < 64) :
    (Sym.bin .shl .W64 x (.lit j)).eval env = x.eval env <<< j := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  congr 1
  simp only [low, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by
    show j < 2 ^ 8; omega)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)

omit [Labels] in
theorem shl4_toNat' (x : BitVec 64) (h : x.toNat < 2 ^ 60) : (x <<< 4).toNat = 16 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

omit [Labels] in
/-- `movl %r15d, %edx; andl $254, %edx`: the count rounded down to even, for a count up to `160`. -/
theorem and254 : ∀ n < 161,
    (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 254)).toNat =
      2 * (n / 2) := by
  decide +kernel

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
