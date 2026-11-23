module

public import NativeRustcArm.Sym.Smart

/-!
# Symbolic flags are sound

The symbolic flags of `SUBS`, `ADDS` and the logical instructions are Kraken's
(`eval_subsFlags`, `eval_addsFlags`, `eval_logicFlags`), with the carry of a subtraction as an
unsigned comparison and its zero flag as an equality; a symbolic condition is Kraken's condition
code on the flags (`eval_condSym`).
-/

namespace NativeRustcArm.Sym

public section

theorem sub_beq_zero {n : Nat} (x y : BitVec n) : ((x - y) == BitVec.zero n) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact bv_sub_eq_zero x y

theorem subs_carry {n : Nat} (x y : BitVec n) :
    ((x - y).unsigned == x.unsigned - y.unsigned) = !x.ult y := by
  simp only [BitVec.unsigned, BitVec.ult, BitVec.toNat_sub]
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.toNat < y.toNat
  · have h1 : ((2 ^ n - y.toNat + x.toNat) % 2 ^ n : Nat) = 2 ^ n - y.toNat + x.toNat := by
      apply Nat.mod_eq_of_lt
      omega
    simp only [h1, decide_eq_true h, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    omega
  · have h1 : ((2 ^ n - y.toNat + x.toNat) % 2 ^ n : Nat) = x.toNat - y.toNat := by
      rw [show 2 ^ n - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [h1, decide_eq_false h, Bool.not_false, beq_iff_eq]
    omega

variable [Labels] (env : Env)

@[simp] theorem eval_subsFlags (w : RegWidth) (a b : Sym) :
    (subsFlags w a b).eval env =
      StatusFlags.subs (low w (a.eval env) - low w (b.eval env)) (low w (a.eval env))
        (low w (b.eval env)) := by
  simp only [subsFlags, SFlags.eval, eval_mkMsb, eval_mkBin, eval_mkCmp, eval_mkNot,
    BinOp.apply, CmpOp.apply, low_ext, StatusFlags.subs, StatusFlags.from_result, sub_beq_zero,
    subs_carry]

@[simp] theorem eval_addsFlags (w : RegWidth) (a b : Sym) :
    (addsFlags w a b).eval env =
      StatusFlags.adds (low w (a.eval env) + low w (b.eval env)) (low w (a.eval env))
        (low w (b.eval env)) := by
  simp only [addsFlags, SFlags.eval, eval_mkMsb, eval_mkBin, eval_mkCmp, BinOp.apply,
    CmpOp.apply, low_ext, StatusFlags.adds, StatusFlags.from_result, Sym.eval, low_zero]
  rfl

@[simp] theorem eval_logicFlags (w : RegWidth) (r : Sym) :
    (logicFlags w r).eval env =
      StatusFlags.from_result (low w (r.eval env)) { c := false, v := false } := by
  simp only [logicFlags, SFlags.eval, eval_mkMsb, eval_mkCmp, CmpOp.apply, Sym.eval, low_zero,
    StatusFlags.from_result]
  rfl

omit [Labels] in
theorem eval_nzcvFlags [Labels] (nzcv : Nat) : (nzcvFlags nzcv).eval env = StatusFlags.ofNat nzcv :=
  rfl

@[simp] theorem eval_SFlags_ite (c : SBool) (f g : SFlags) :
    (SFlags.ite c f g).eval env = if c.eval env then f.eval env else g.eval env := by
  simp only [SFlags.ite, SFlags.eval, eval_mkIteB]
  split <;> rfl

@[simp] theorem eval_condSym (cc : CondCode) (f : SFlags) :
    (condSym cc f).eval env = cc.interp (f.eval env) := by
  cases cc <;> simp only [condSym, SFlags.eval, CondCode.interp, SBool.eval, eval_mkNot,
    eval_mkAnd, eval_mkOr, eval_mkBeq] <;>
    cases SBool.eval env f.n <;> cases SBool.eval env f.v <;> cases SBool.eval env f.z <;> rfl

end

end NativeRustcArm.Sym
