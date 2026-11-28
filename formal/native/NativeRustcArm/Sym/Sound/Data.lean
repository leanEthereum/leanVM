module

public import NativeRustcArm.Sym.Operand

/-!
# Data-processing instructions are sound

`OpOk` for the arithmetic, logical, bitfield, move-wide, conditional-select and conditional-compare
instructions: one lemma per symbolic step family (`Step.shifted`, `Step.arithE`, ...) from the
value Kraken computes, then one per `Operation` constructor.
-/

namespace NativeRustcArm.Sym

public section

variable [Labels] {env : Env} {S S' : SState} {x : Exit} {m : MachineData} {w : RegWidth}

/-! ## Step families -/

theorem shifted_ok (op : BinOp) (f : w.type → w.type → w.type)
    (hf : ∀ a b, op.apply w a b = ext w (f (low w a) (low w b)))
    {dst src1 : RegOrZr w} {src2 : ShiftRegExpr w} (hm : Match env S m)
    (h : Step.shifted op dst src1 src2 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (f (m.regs.getRegOrZr src1) (src2.interp m.regs p))) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.shifted, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [eval_mkBin, hf, hm.getZr ha, hm.shiftOp hb p]

theorem shiftedFlags_ok (op : BinOp) (f : w.type → w.type → w.type)
    (hf : ∀ a b, op.apply w a b = ext w (f (low w a) (low w b)))
    {dst src1 : RegOrZr w} {src2 : ShiftRegExpr w} (hm : Match env S m)
    (h : Step.shiftedFlags op dst src1 src2 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨
      let res := f (m.regs.getRegOrZr src1) (src2.interp m.regs p)
      let m₁ := { m with status := StatusFlags.from_result res { c := false, v := false } }
      { m₁ with regs := m₁.regs.setRegOrZr dst res }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.shiftedFlags, Option.bind_eq_bind, Option.bind_eq_some_iff, fall,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  have hr : (mkBin op w a b).eval env = ext w (f (m.regs.getRegOrZr src1) (src2.interp m.regs p)) := by
    rw [eval_mkBin, hf, hm.getZr ha, hm.shiftOp hb p]
  refine done_fall ((hm.setFlags _ ?_).setZr dst hr)
  rw [eval_logicFlags, hr, low_ext]

theorem logicI_ok (op : BinOp) (f : w.type → w.type → w.type)
    (hf : ∀ a b, op.apply w a b = ext w (f (low w a) (low w b)))
    {dst : RegOrSp w} {src1 : RegOrZr w} {imm : ConstExpr} (hm : Match env S m)
    (h : Step.logicI op dst src1 imm S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrSp dst
      (f (m.regs.getRegOrZr src1) (BitVec.ofInt w.bits (imm.interp p).toInt))) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.logicI, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall (hm.setSp dst ?_)
  rw [eval_mkBin, hf, hm.getZr ha, logicImm_spec hb p]

theorem andsI_ok {dst src1 : RegOrZr w} {imm : ConstExpr} (hm : Match env S m)
    (h : Step.andsI dst src1 imm S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨
      let res := m.regs.getRegOrZr src1 &&& BitVec.ofInt w.bits (imm.interp p).toInt
      let m₁ := { m with status := StatusFlags.from_result res { c := false, v := false } }
      { m₁ with regs := m₁.regs.setRegOrZr dst res }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.andsI, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  have hr : (mkBin .and w a b).eval env =
      ext w (m.regs.getRegOrZr src1 &&& BitVec.ofInt w.bits (imm.interp p).toInt) := by
    rw [eval_mkBin, hm.getZr ha, logicImm_spec hb p]
    rfl
  refine done_fall ((hm.setFlags _ ?_).setZr dst hr)
  rw [eval_logicFlags, hr, low_ext]

theorem arithE_ok (op : BinOp) (f : w.type → w.type → w.type)
    (hf : ∀ a b, op.apply w a b = ext w (f (low w a) (low w b)))
    {dst src1 : RegOrSp w} {src2 : ExtOrImmReg} (hm : Match env S m)
    (h : Step.arithE op dst src1 src2 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrSp dst
      (f (m.regs.getRegOrSp src1) (src2.interp m.regs p))) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.arithE, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall (hm.setSp dst ?_)
  rw [eval_mkBin, hf, hm.getSp ha, hm.extOrImm hb p]

theorem arithFlagsE_sub_ok {dst : RegOrZr w} {src1 : RegOrSp w} {src2 : ExtOrImmReg}
    (hm : Match env S m) (h : Step.arithFlagsE true dst src1 src2 S = some (S', x))
    (p : Std.Rco Int64) :
    (Effects.done ⟨
      let val1 := m.regs.getRegOrSp src1
      let val2 : w.type := src2.interp m.regs p
      let m₁ := { m with status := StatusFlags.subs (val1 - val2) val1 val2 }
      { m₁ with regs := m₁.regs.setRegOrZr dst (val1 - val2) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.arithFlagsE, Option.bind_eq_bind, Option.bind_eq_some_iff, fall,
    Option.some.injEq, Prod.mk.injEq, ite_true] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall ((hm.setFlags _ ?_).setZr dst ?_)
  · rw [eval_subsFlags, hm.getSp ha, hm.extOrImm hb p]
  · rw [eval_mkBin, hm.getSp ha, hm.extOrImm hb p]
    rfl

theorem arithFlagsE_add_ok {dst : RegOrZr w} {src1 : RegOrSp w} {src2 : ExtOrImmReg}
    (hm : Match env S m) (h : Step.arithFlagsE false dst src1 src2 S = some (S', x))
    (p : Std.Rco Int64) :
    (Effects.done ⟨
      let val1 := m.regs.getRegOrSp src1
      let val2 : w.type := src2.interp m.regs p
      let m₁ := { m with status := StatusFlags.adds (val1 + val2) val1 val2 }
      { m₁ with regs := m₁.regs.setRegOrZr dst (val1 + val2) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.arithFlagsE, Option.bind_eq_bind, Option.bind_eq_some_iff, fall,
    Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall ((hm.setFlags _ ?_).setZr dst ?_)
  · rw [eval_addsFlags, hm.getSp ha, hm.extOrImm hb p]
  · rw [eval_mkBin, hm.getSp ha, hm.extOrImm hb p]
    rfl

theorem arithFlagsS_sub_ok {dst src1 : RegOrZr w} {src2 : ShiftRegExpr w}
    (hm : Match env S m) (h : Step.arithFlagsS true dst src1 src2 S = some (S', x))
    (p : Std.Rco Int64) :
    (Effects.done ⟨
      let val1 := m.regs.getRegOrZr src1
      let val2 := src2.interp m.regs p
      let m₁ := { m with status := StatusFlags.subs (val1 - val2) val1 val2 }
      { m₁ with regs := m₁.regs.setRegOrZr dst (val1 - val2) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.arithFlagsS, Option.bind_eq_bind, Option.bind_eq_some_iff, fall,
    Option.some.injEq, Prod.mk.injEq, ite_true] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall ((hm.setFlags _ ?_).setZr dst ?_)
  · rw [eval_subsFlags, hm.getZr ha, hm.shiftOp hb p]
  · rw [eval_mkBin, hm.getZr ha, hm.shiftOp hb p]
    rfl

theorem arithFlagsS_add_ok {dst src1 : RegOrZr w} {src2 : ShiftRegExpr w}
    (hm : Match env S m) (h : Step.arithFlagsS false dst src1 src2 S = some (S', x))
    (p : Std.Rco Int64) :
    (Effects.done ⟨
      let val1 := m.regs.getRegOrZr src1
      let val2 := src2.interp m.regs p
      let m₁ := { m with status := StatusFlags.adds (val1 + val2) val1 val2 }
      { m₁ with regs := m₁.regs.setRegOrZr dst (val1 + val2) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.arithFlagsS, Option.bind_eq_bind, Option.bind_eq_some_iff, fall,
    Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall ((hm.setFlags _ ?_).setZr dst ?_)
  · rw [eval_addsFlags, hm.getZr ha, hm.shiftOp hb p]
  · rw [eval_mkBin, hm.getZr ha, hm.shiftOp hb p]
    rfl

theorem reg3_ok (op : BinOp) (f : w.type → w.type → w.type)
    (hf : ∀ a b, op.apply w a b = ext w (f (low w a) (low w b)))
    {dst src1 src2 : RegOrZr w} (hm : Match env S m)
    (h : Step.reg3 op dst src1 src2 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (f (m.regs.getRegOrZr src1) (m.regs.getRegOrZr src2))) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.reg3, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [eval_mkBin, hf, hm.getZr ha, hm.getZr hb]

theorem mulAcc_add_ok {dst src1 src2 src3 : RegOrZr w} (hm : Match env S m)
    (h : Step.mulAcc false dst src1 src2 src3 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (m.regs.getRegOrZr src1 * m.regs.getRegOrZr src2 + m.regs.getRegOrZr src3)) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.mulAcc, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq, Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  simp only [eval_mkBin, BinOp.apply, low_ext, hm.getZr ha, hm.getZr hb, hm.getZr hc]

theorem mulAcc_sub_ok {dst src1 src2 src3 : RegOrZr w} (hm : Match env S m)
    (h : Step.mulAcc true dst src1 src2 src3 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (m.regs.getRegOrZr src3 - m.regs.getRegOrZr src1 * m.regs.getRegOrZr src2)) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.mulAcc, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq, ite_true] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  simp only [eval_mkBin, BinOp.apply, low_ext, hm.getZr ha, hm.getZr hb, hm.getZr hc]

omit [Labels] in
theorem umaddl_eq (x y : BitVec 32) (z : BitVec 64) :
    ext .W32 x * ext .W32 y + z = BitVec.ofInt 64 (x.unsigned * y.unsigned + z.unsigned) := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.unsigned, BitVec.unsigned, BitVec.unsigned,
    show (x.toNat : Int) * y.toNat + z.toNat = ((x.toNat * y.toNat + z.toNat : Nat) : Int) by
      push_cast; rfl,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul, ext_W32, ext_W32,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)), Nat.mod_add_mod]

theorem umaddl_ok {dst : RegOrZr .W64} {src1 src2 : RegOrZr .W32} {src3 : RegOrZr .W64}
    (hm : Match env S m) (h : Step.umaddl dst src1 src2 src3 S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst (BitVec.ofInt 64
      ((m.regs.getRegOrZr src1).unsigned * (m.regs.getRegOrZr src2).unsigned +
        (m.regs.getRegOrZr src3).unsigned))) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.umaddl, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [hm.getZr ha, hm.getZr hb, hm.getZr hc, ← umaddl_eq]
  simp only [eval_mkBin, BinOp.apply, eval_truncTo, low_W64, ext_W64]

theorem unary_ok (op : UnOp) (f : w.type → w.type) (hf : ∀ a, op.apply w a = ext w (f (low w a)))
    {dst src : RegOrZr w} (hm : Match env S m) (h : Step.unary op dst src S = some (S', x))
    (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := m.regs.setRegOrZr dst (f (m.regs.getRegOrZr src)) },
      p.upper⟩).All (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.unary, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [eval_mkUn, hf, hm.getZr ha]

theorem bfm_ok {dst src : RegOrZr w} {immr imms : Nat} (hm : Match env S m)
    (h : Step.bfm dst src immr imms S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (evalBFM (m.regs.getRegOrZr dst) (m.regs.getRegOrZr src) immr imms)) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.bfm, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨d, hd, a, ha, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [eval_mkBin, hm.getZr hd, hm.getZr ha]
  rfl

theorem movVal_spec {imm : ConstExpr} {sh : MovShift w} {v : BitVec w.bits}
    (h : Step.movVal w imm sh = some v) (p : Std.Rco Int64) :
    (BitVec.ofInt w.bits (imm.interp p).toInt &&& 0xFFFF#w.bits) <<< sh.toNat = v := by
  unfold Step.movVal at h
  split at h
  · cases h
    rfl
  · cases h

theorem movzn_ok (inv : Bool) {dst : RegOrZr w} {imm : ConstExpr} {sh : MovShift w}
    (hm : Match env S m) (h : Step.movzn inv dst imm sh S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (if inv then ~~~((BitVec.ofInt w.bits (imm.interp p).toInt &&& 0xFFFF#w.bits) <<< sh.toNat)
        else (BitVec.ofInt w.bits (imm.interp p).toInt &&& 0xFFFF#w.bits) <<< sh.toNat)) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.movzn, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨v, hv, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [eval_lit_toNat, movVal_spec hv p]

theorem movk_ok {dst : RegOrZr w} {imm : ConstExpr} {sh : MovShift w}
    (hm : Match env S m) (h : Step.movk dst imm sh S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      ((m.regs.getRegOrZr dst &&& ~~~(0xFFFF#w.bits <<< sh.toNat)) |||
        ((BitVec.ofInt w.bits (imm.interp p).toInt &&& 0xFFFF#w.bits) <<< sh.toNat))) },
      p.upper⟩).All (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.movk, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨old, hold, v, hv, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  simp only [eval_mkBin, BinOp.apply, eval_lit_toNat, low_ext, hm.getZr hold, movVal_spec hv p]

theorem csel_ok (op : UnOp) (f : w.type → w.type) (hf : ∀ a, op.apply w a = ext w (f (low w a)))
    {dst src1 src2 : RegOrZr w} {cond : CondCode} (hm : Match env S m)
    (h : Step.csel op dst src1 src2 cond S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr dst
      (if cond.interp m.status then m.regs.getRegOrZr src1 else f (m.regs.getRegOrZr src2))) },
      p.upper⟩).All (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.csel, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨fl, hfl, a, ha, b, hb, rfl, rfl⟩ := h
  refine done_fall (hm.setZr dst ?_)
  rw [eval_mkIte, eval_condSym, eval_truncTo, eval_mkUn, hf, ← hm.flagsEq hfl, hm.getZr ha,
    hm.getZr hb]
  split <;> rfl

theorem ccmp_ok (sub : Bool) {src1 : RegOrZr w} {b : Option Sym} {nzcv : Nat} {cond : CondCode}
    (val2 : w.type) (hb : ∀ u, b = some u → low w (u.eval env) = val2) (hm : Match env S m)
    (h : Step.ccmp sub src1 b nzcv cond S = some (S', x)) (p : Std.Rco Int64) :
    (Effects.done ⟨{ m with status :=
      (if CondCode.interp cond m.status then
        (if sub then StatusFlags.subs (m.regs.getRegOrZr src1 - val2) (m.regs.getRegOrZr src1) val2
        else StatusFlags.adds (m.regs.getRegOrZr src1 + val2) (m.regs.getRegOrZr src1) val2)
      else StatusFlags.ofNat nzcv) }, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.ccmp, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨fl, hfl, a, ha, u, hu, rfl, rfl⟩ := h
  refine done_fall (hm.setFlags _ ?_)
  rw [eval_SFlags_ite, eval_condSym, ← hm.flagsEq hfl, eval_nzcvFlags, hm.getZr ha, ← hb u hu]
  cases sub <;> simp only [Bool.false_eq_true, ite_true, ite_false, eval_subsFlags, eval_addsFlags]

/-! ## Instructions -/

theorem ok_ADD_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.ADD_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .add (· + ·) (fun _ _ => rfl) hm h p

theorem ok_SUB_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.SUB_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .sub (· - ·) (fun _ _ => rfl) hm h p

theorem ok_AND_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.AND_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .and (· &&& ·) (fun _ _ => rfl) hm h p

theorem ok_ORR_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.ORR_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .orr (· ||| ·) (fun _ _ => rfl) hm h p

theorem ok_ORN_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.ORN_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .orn (fun a b => a ||| ~~~b) (fun _ _ => rfl) hm h p

theorem ok_EOR_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.EOR_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .eor (· ^^^ ·) (fun _ _ => rfl) hm h p

theorem ok_EON_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.EON_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .eon (fun a b => a ^^^ ~~~b) (fun _ _ => rfl) hm h p

theorem ok_BIC_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : OpOk env (.BIC_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shifted_ok .bic (fun a b => a &&& ~~~b) (fun _ _ => rfl) hm h p

theorem ok_ANDS_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    OpOk env (.ANDS_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shiftedFlags_ok .and (· &&& ·) (fun _ _ => rfl) hm h p

theorem ok_BICS_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    OpOk env (.BICS_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => shiftedFlags_ok .bic (fun a b => a &&& ~~~b) (fun _ _ => rfl) hm h p

theorem ok_AND_i (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) :
    OpOk env (.AND_i dst src1 imm) :=
  fun _ _ _ _ p _ hm h => logicI_ok .and (· &&& ·) (fun _ _ => rfl) hm h p

theorem ok_ORR_i (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) :
    OpOk env (.ORR_i dst src1 imm) :=
  fun _ _ _ _ p _ hm h => logicI_ok .orr (· ||| ·) (fun _ _ => rfl) hm h p

theorem ok_EOR_i (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) :
    OpOk env (.EOR_i dst src1 imm) :=
  fun _ _ _ _ p _ hm h => logicI_ok .eor (· ^^^ ·) (fun _ _ => rfl) hm h p

theorem ok_ANDS_i (dst src1 : RegOrZr w) (imm : ConstExpr) : OpOk env (.ANDS_i dst src1 imm) :=
  fun _ _ _ _ p _ hm h => andsI_ok hm h p

theorem ok_ADD_e (dst src1 : RegOrSp w) (src2 : ExtOrImmReg) : OpOk env (.ADD_e dst src1 src2) :=
  fun _ _ _ _ p _ hm h => arithE_ok .add (· + ·) (fun _ _ => rfl) hm h p

theorem ok_SUB_e (dst src1 : RegOrSp w) (src2 : ExtOrImmReg) : OpOk env (.SUB_e dst src1 src2) :=
  fun _ _ _ _ p _ hm h => arithE_ok .sub (· - ·) (fun _ _ => rfl) hm h p

theorem ok_ADDS_e (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) :
    OpOk env (.ADDS_e dst src1 src2) :=
  fun _ _ _ _ p _ hm h => arithFlagsE_add_ok hm h p

theorem ok_SUBS_e (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) :
    OpOk env (.SUBS_e dst src1 src2) :=
  fun _ _ _ _ p _ hm h => arithFlagsE_sub_ok hm h p

theorem ok_ADDS_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    OpOk env (.ADDS_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => arithFlagsS_add_ok hm h p

theorem ok_SUBS_s (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    OpOk env (.SUBS_s dst src1 src2) :=
  fun _ _ _ _ p _ hm h => arithFlagsS_sub_ok hm h p

theorem ok_MADD (dst src1 src2 src3 : RegOrZr w) : OpOk env (.MADD dst src1 src2 src3) :=
  fun _ _ _ _ p _ hm h => mulAcc_add_ok hm h p

theorem ok_MSUB (dst src1 src2 src3 : RegOrZr w) : OpOk env (.MSUB dst src1 src2 src3) :=
  fun _ _ _ _ p _ hm h => mulAcc_sub_ok hm h p

theorem ok_UMULH (dst src1 src2 : RegOrZr .W64) : OpOk env (.UMULH dst src1 src2) :=
  fun _ _ _ _ p _ hm h => reg3_ok .umulh
    (fun a b => (BitVec.ofInt (64 + 64) (a.unsigned * b.unsigned)).extractLsb' 64 64)
    (fun _ _ => rfl) hm h p

theorem ok_UMADDL (dst : RegOrZr .W64) (src1 src2 : RegOrZr .W32) (src3 : RegOrZr .W64) :
    OpOk env (.UMADDL dst src1 src2 src3) :=
  fun _ _ _ _ p _ hm h => umaddl_ok hm h p

theorem ok_EXTR (dst src1 src2 : RegOrZr w) (lsb : Nat) : OpOk env (.EXTR dst src1 src2 lsb) :=
  fun _ _ _ _ p _ hm h => reg3_ok (.extr lsb)
    (fun a b => if lsb % w.bits == 0 then b else (a <<< (w.bits - lsb % w.bits)) ||| (b >>> (lsb % w.bits)))
    (fun _ _ => rfl) hm h p

theorem ok_LSLV (dst src1 src2 : RegOrZr w) : OpOk env (.LSLV dst src1 src2) :=
  fun _ _ _ _ p _ hm h => reg3_ok .lslv (fun a b => a <<< (b.toNat % w.bits)) (fun _ _ => rfl) hm h p

theorem ok_LSRV (dst src1 src2 : RegOrZr w) : OpOk env (.LSRV dst src1 src2) :=
  fun _ _ _ _ p _ hm h => reg3_ok .lsrv (fun a b => a.ushiftRight (b.toNat % w.bits))
    (fun _ _ => rfl) hm h p

theorem ok_ASRV (dst src1 src2 : RegOrZr w) : OpOk env (.ASRV dst src1 src2) :=
  fun _ _ _ _ p _ hm h => reg3_ok .asrv (fun a b => a.sshiftRight (b.toNat % w.bits))
    (fun _ _ => rfl) hm h p

theorem ok_RORV (dst src1 src2 : RegOrZr w) : OpOk env (.RORV dst src1 src2) :=
  fun _ _ _ _ p _ hm h => reg3_ok .rorv (fun a b => a.rotateRight (b.toNat % w.bits))
    (fun _ _ => rfl) hm h p

theorem ok_BFM (dst src : RegOrZr w) (immr imms : Nat) : OpOk env (.BFM dst src immr imms) :=
  fun _ _ _ _ p _ hm h => bfm_ok hm h p

theorem ok_SBFM (dst src : RegOrZr w) (immr imms : Nat) : OpOk env (.SBFM dst src immr imms) :=
  fun _ _ _ _ p _ hm h => unary_ok (.sbfm immr imms) (evalSBFM · immr imms) (fun _ => rfl) hm h p

theorem ok_UBFM (dst src : RegOrZr w) (immr imms : Nat) : OpOk env (.UBFM dst src immr imms) :=
  fun _ _ _ _ p _ hm h => unary_ok (.ubfm immr imms) (evalUBFM · immr imms) (fun _ => rfl) hm h p

theorem ok_REV (dst src : RegOrZr w) : OpOk env (.REV dst src) := by
  intro _ _ _ _ p _ hm h
  have := unary_ok .rev (revW w) (fun _ => rfl) hm h p
  cases w <;> exact this

theorem ok_RBIT (dst src : RegOrZr w) : OpOk env (.RBIT dst src) :=
  fun _ _ _ _ p _ hm h => unary_ok .rbit BitVec.reverse (fun _ => rfl) hm h p

theorem ok_MOVZ (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w) :
    OpOk env (.MOVZ dst imm sh) :=
  fun _ _ _ _ p _ hm h => movzn_ok false hm h p

theorem ok_MOVN (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w) :
    OpOk env (.MOVN dst imm sh) :=
  fun _ _ _ _ p _ hm h => movzn_ok true hm h p

theorem ok_MOVK (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w) :
    OpOk env (.MOVK dst imm sh) :=
  fun _ _ _ _ p _ hm h => movk_ok hm h p

theorem ok_CSEL (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    OpOk env (.CSEL dst src1 src2 cond) :=
  fun _ _ _ _ p _ hm h => csel_ok .trunc id (fun _ => rfl) hm h p

theorem ok_CSINC (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    OpOk env (.CSINC dst src1 src2 cond) :=
  fun _ _ _ _ p _ hm h => csel_ok .inc (· + 1#w.bits) (fun _ => rfl) hm h p

theorem ok_CSINV (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    OpOk env (.CSINV dst src1 src2 cond) :=
  fun _ _ _ _ p _ hm h => csel_ok .not (~~~·) (fun _ => rfl) hm h p

theorem ok_CSNEG (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    OpOk env (.CSNEG dst src1 src2 cond) :=
  fun _ _ _ _ p _ hm h => csel_ok .neg (-·) (fun _ => rfl) hm h p

theorem ok_CCMP_reg (src1 src2 : RegOrZr w) (nzcv : Nat) (cond : CondCode) :
    OpOk env (.CCMP_reg src1 src2 nzcv cond) := by
  intro S _ _ m p _ hm h
  exact ccmp_ok true (m.regs.getRegOrZr src2) (fun _ hu => (hm.getZr hu).symm) hm h p

theorem ok_CCMN_reg (src1 src2 : RegOrZr w) (nzcv : Nat) (cond : CondCode) :
    OpOk env (.CCMN_reg src1 src2 nzcv cond) := by
  intro S _ _ m p _ hm h
  exact ccmp_ok false (m.regs.getRegOrZr src2) (fun _ hu => (hm.getZr hu).symm) hm h p

theorem ok_CCMP_imm (src1 : RegOrZr w) (imm nzcv : Nat) (cond : CondCode) :
    OpOk env (.CCMP_imm src1 imm nzcv cond) := by
  intro S _ _ m p _ hm h
  exact ccmp_ok true (BitVec.ofNat w.bits imm)
    (fun _ hu => by cases hu; rw [eval_lit_toNat, low_ext]) hm h p

theorem ok_CCMN_imm (src1 : RegOrZr w) (imm nzcv : Nat) (cond : CondCode) :
    OpOk env (.CCMN_imm src1 imm nzcv cond) := by
  intro S _ _ m p _ hm h
  exact ccmp_ok false (BitVec.ofNat w.bits imm)
    (fun _ hu => by cases hu; rw [eval_lit_toNat, low_ext]) hm h p

end

end NativeRustcArm.Sym
