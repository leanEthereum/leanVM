module

public import NativeRustcArm.Sym
public import NativeVm.Model.KeccakGkr
import Mathlib.Tactic.IntervalCases

/-!
# `verify_layer`'s index arithmetic

The layer's weights loop (`b57`, `b60`) computes, from `j = X19 < 1600`, the lane's column
(`(j / 64) % 5`, by `umulh`), `5 * (j / 320)`, and the positions `keccakAlong j 4` and
`keccakAlong j 3` less `j % 64` (`x11S`, `x9b`).

Each value is read off a symbolic term by the evaluation's equations on constructors with free
subterms (`ev_bin`, `ev_un`, …) and arithmetic on `BitVec` variables: the kernel never unfolds
the evaluation of a literal term.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Protocol.Verifier

@[expose] public section

/-- `j / 64`. -/
def Lsym : Sym := .un (.ubfm 6 63) .W64 (.reg .X19)
/-- `(j / 64) / 5`. -/
def Qsym : Sym := .bin .umulh .W64 Lsym (.lit 3689348814741910324)
/-- `5 ((j / 64) / 5)`. -/
def Fsym : Sym := .bin .add .W64 Qsym (.un (.shift .LSL 2) .W64 Qsym)
/-- `j · 4/5`. -/
def Psym : Sym := .bin .umulh .W64 (.reg .X19) (.lit 14757395258967641293)
/-- `j / 320`. -/
def Rsym : Sym := .un (.ubfm 8 63) .W64 Psym
/-- `5 (j / 320)`. -/
def Tsym : Sym := .bin .add .W64 Rsym (.un (.shift .LSL 2) .W64 Rsym)
/-- `(j / 64) % 5`. -/
def x9S : Sym := .bin .sub .W64 Lsym Fsym
/-- `((j / 64) % 5 + 4) % 5`. -/
def x8S : Sym := .ite (.cmp .eq .W64 Lsym Fsym) (.lit 4) (.bin .sub .W64 x9S (.lit 1))
/-- `64 (((j / 64) % 5 + 4) % 5 + 5 (j / 320))`. -/
def x11S : Sym := .un (.ubfm 58 57) .W64 (.bin .add .W64 x8S Tsym)
/-- `64 (X10 + (X9 + 3) % 5)`, for `X9 < 5`. -/
def x9b : Sym :=
  .un (.ubfm 58 57) .W64 (.bin .add .W64 (.bin .add .W64 (.reg .X10) (.reg .X9))
    (.ite (.cmp .ult .W64 (.reg .X9) (.lit 2)) (.lit 3) (.lit 288230376151711742)))

/-- The position `keccakAlong j k` less `j % 64`, over `64`. -/
def alongRow (j k : Nat) : Nat := ((j / 64) % 5 + k) % 5 + 5 * (j / 320)

end

public section

/-! ## Operations on `BitVec` variables -/

theorem umulh_toNat' (a b : BitVec 64) :
    (BinOp.apply .umulh .W64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    BitVec.unsigned]
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb
    simpa using this
  rw [show ((a.toNat : Int) * (b.toNat : Int)) = ((a.toNat * b.toNat : Nat) : Int) by
    push_cast; rfl]
  have hw : RegWidth.W64.bits = 64 := rfl
  rw [hw, Nat.shiftRight_eq_div_pow]
  omega

theorem lsr_toNat (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (UnOp.apply (.ubfm k 63) .W64 x).toNat = x.toNat / 2 ^ k := by
  have hb : RegWidth.W64.bits = 64 := rfl
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, evalUBFM, hb, Nat.mod_eq_of_lt hk,
    show 63 % 64 = 63 from rfl, show 63 ≥ k from by omega, ↓reduceIte, BitVec.toNat_setWidth,
    BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have h1 : x.toNat / 2 ^ k < 2 ^ (63 - k + 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 63 - k + 1 + k = 64 by omega]
    exact x.isLt
  have h2 : 2 ^ (63 - k + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [Nat.pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

theorem lsl6_toNat (x : BitVec 64) :
    (UnOp.apply (.ubfm 58 57) .W64 x).toNat = x.toNat * 64 % 2 ^ 64 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, evalUBFM, BitVec.take]
  simp only [show RegWidth.W64.bits = 64 from rfl]
  simp
  omega

theorem shl2_toNat (x : BitVec 64) :
    (UnOp.apply (.shift .LSL 2) .W64 x).toNat = x.toNat * 4 % 2 ^ 64 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]

theorem shl4_toNat (x : BitVec 64) :
    (UnOp.apply (.shift .LSL 4) .W64 x).toNat = x.toNat * 16 % 2 ^ 64 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]

theorem add_toNat (x y : BitVec 64) :
    (BinOp.apply .add .W64 x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_add]

theorem sub_toNat (x y : BitVec 64) :
    (BinOp.apply .sub .W64 x y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub]

theorem and63_toNat (x : BitVec 64) :
    (BinOp.apply .and .W64 x (BitVec.ofNat 64 63)).toNat = x.toNat % 64 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `q + 4 q` for a small `q`. -/
theorem add_shl2_toNat (x : BitVec 64) (h : x.toNat < 2 ^ 61) :
    (BinOp.apply .add .W64 x (UnOp.apply (.shift .LSL 2) .W64 x)).toNat = 5 * x.toNat := by
  rw [add_toNat, shl2_toNat]
  omega

/-- `x` and `y` equal as numbers. -/
theorem eq_apply (x y : BitVec 64) : CmpOp.apply .eq .W64 x y = decide (x.toNat = y.toNat) := by
  simp only [CmpOp.apply, Sym.low_W64]
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun e ↦ h (BitVec.eq_of_toNat_eq e)
    simp [h, this]

theorem ult_apply (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  simp only [CmpOp.apply, Sym.low_W64, BitVec.ult]

/-! ## Magic numbers -/

theorem div5_magic (x : Nat) (hx : x < 25) : x * 3689348814741910324 / 2 ^ 64 = x / 5 := by
  interval_cases x <;> rfl

theorem div320_aux (q r : Nat) (hq : q < 5) (hr : r < 320) :
    (320 * q + r) * 14757395258967641293 / 2 ^ 64 / 2 ^ 8 = (320 * q + r) / 320 := by
  rw [Nat.div_div_eq_div_mul]
  have e : (320 * q + r) * 14757395258967641293 =
      q * 2 ^ 72 + (64 * q + r * 14757395258967641293) := by
    omega
  rw [e, show 2 ^ 64 * 2 ^ 8 = 2 ^ 72 by rfl, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide)]
  have : 64 * q + r * 14757395258967641293 < 2 ^ 72 := by
    have : r * 14757395258967641293 ≤ 319 * 14757395258967641293 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (319 * 14757395258967641293 : Nat) + 64 * 4 < 2 ^ 72 := by decide
    omega
  rw [Nat.div_eq_of_lt this]
  omega

theorem div320_magic (j : Nat) (hj : j < 1600) :
    j * 14757395258967641293 / 2 ^ 64 / 2 ^ 8 = j / 320 := by
  have := div320_aux (j / 320) (j % 320) (by omega) (by omega)
  rwa [Nat.div_add_mod] at this

/-! ## The evaluation on constructors -/

variable [Labels] {env : Env}

theorem ev_bin (op : BinOp) (w : RegWidth) (a b : Sym) :
    (Sym.bin op w a b).eval env = op.apply w (a.eval env) (b.eval env) := by
  rw [Sym.eval]

theorem ev_un (op : UnOp) (w : RegWidth) (a : Sym) :
    (Sym.un op w a).eval env = op.apply w (a.eval env) := by
  rw [Sym.eval]

theorem ev_lit (n : Nat) : (Sym.lit n).eval env = BitVec.ofNat 64 n := by
  rw [Sym.eval]

theorem ev_reg (r : XReg) : (Sym.reg r).eval env = env.regs r := by
  rw [Sym.eval]

theorem ev_ite (c : SBool) (a b : Sym) :
    (Sym.ite c a b).eval env = if c.eval env then a.eval env else b.eval env := by
  rw [Sym.eval]

theorem sb_cmp (op : CmpOp) (w : RegWidth) (a b : Sym) :
    (SBool.cmp op w a b).eval env = op.apply w (a.eval env) (b.eval env) := by
  rw [SBool.eval]

theorem ev_load (r o n : Nat) : (Sym.load r o n).eval env = env.load r o n := by
  rw [Sym.eval]

theorem ev_ptr (r : Nat) (o : Int) : (Sym.ptr r o).eval env = env.base r + BitVec.ofInt 64 o := by
  rw [Sym.eval]

theorem sb_not (b : SBool) : (SBool.not b).eval env = !b.eval env := by
  rw [SBool.eval]

theorem sb_and (b c : SBool) : (SBool.and b c).eval env = (b.eval env && c.eval env) := by
  rw [SBool.eval]

theorem sb_or (b c : SBool) : (SBool.or b c).eval env = (b.eval env || c.eval env) := by
  rw [SBool.eval]

/-! ## The values -/

variable {j : Nat}

theorem L_val (hj : (env.regs .X19).toNat = j) : (Lsym.eval env).toNat = j / 64 := by
  rw [Lsym, ev_un, ev_reg, lsr_toNat _ (by decide), hj]
  rfl

theorem Q_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (Qsym.eval env).toNat = j / 64 / 5 := by
  rw [Qsym, ev_bin, umulh_toNat', L_val hj, ev_lit, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 3689348814741910324 < 2 ^ 64 by decide), div5_magic _ (by omega)]

theorem F_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (Fsym.eval env).toNat = 5 * (j / 64 / 5) := by
  rw [Fsym, ev_bin, ev_un, add_shl2_toNat _ (by rw [Q_val hj h]; omega), Q_val hj h]

theorem R_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (Rsym.eval env).toNat = j / 320 := by
  rw [Rsym, ev_un, lsr_toNat _ (by decide), Psym, ev_bin, umulh_toNat', ev_reg, hj, ev_lit,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 14757395258967641293 < 2 ^ 64 by decide),
    div320_magic _ h]

theorem T_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (Tsym.eval env).toNat = 5 * (j / 320) := by
  rw [Tsym, ev_bin, ev_un, add_shl2_toNat _ (by rw [R_val hj h]; omega), R_val hj h]

theorem x9S_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (x9S.eval env).toNat = j / 64 % 5 := by
  rw [x9S, ev_bin, sub_toNat, L_val hj, F_val hj h]
  omega

theorem x8S_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (x8S.eval env).toNat = (j / 64 % 5 + 4) % 5 := by
  rw [x8S, ev_ite, sb_cmp, eq_apply, L_val hj, F_val hj h]
  by_cases hc : j / 64 = 5 * (j / 64 / 5)
  · simp only [decide_eq_true hc, ↓reduceIte]
    rw [ev_lit, BitVec.toNat_ofNat]
    omega
  · simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    rw [ev_bin, sub_toNat, x9S_val hj h, ev_lit, BitVec.toNat_ofNat]
    omega

theorem x11S_val (hj : (env.regs .X19).toNat = j) (h : j < 1600) :
    (x11S.eval env).toNat = 64 * alongRow j 4 := by
  rw [x11S, ev_un, lsl6_toNat, ev_bin, add_toNat, x8S_val hj h, T_val hj h, alongRow]
  omega

theorem x9b_val {a b : Nat} (h9 : (env.regs .X9).toNat = a) (h10 : (env.regs .X10).toNat = b)
    (ha : a < 5) (hb : b < 2 ^ 40) :
    (x9b.eval env).toNat = 64 * ((a + 3) % 5 + b) := by
  rw [x9b, ev_un, lsl6_toNat, ev_bin, add_toNat, ev_bin, add_toNat, ev_reg, ev_reg, h9, h10, ev_ite,
    sb_cmp, ult_apply, ev_reg, h9, ev_lit, BitVec.toNat_ofNat]
  by_cases hc : a < 2
  · simp only [decide_eq_true (show a < 2 % 2 ^ 64 by omega), ↓reduceIte]
    rw [ev_lit, BitVec.toNat_ofNat]
    omega
  · simp only [decide_eq_false (show ¬a < 2 % 2 ^ 64 by omega), Bool.false_eq_true, ↓reduceIte]
    rw [ev_lit, BitVec.toNat_ofNat]
    omega

theorem x8_val (hj : (env.regs .X19).toNat = j) :
    ((Sym.bin .and .W64 (.reg .X19) (.lit 63)).eval env).toNat = j % 64 := by
  rw [ev_bin, ev_reg, ev_lit, and63_toNat, hj]

omit [Labels] in
theorem along_eq (j k : Nat) : keccakAlong j k = 64 * alongRow j k + j % 64 := by
  simp only [keccakAlong, alongRow]
  omega

omit [Labels] in
theorem alongRow_lt (j k : Nat) (h : j < 1600) : alongRow j k < 25 := by
  unfold alongRow
  omega

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
