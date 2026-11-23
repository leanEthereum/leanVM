module

public import NativeRustcArm.Sym.Flags
public import NativeRustcArm.Sym.Slots

/-!
# Operands of instructions

`OpOk env op`: from any state the symbolic step of `op` describes, Kraken's semantics of `op`
ends where the step says. The operands the executor reads are Kraken's: shifted registers
(`Match.shiftOp`), extended registers and immediates (`Match.extOrImm`, `Match.logicImm`), branch
targets (`target_spec`); the values Kraken loads and stores (`ext_load`, `store_bytes`).
-/

namespace NativeRustcArm.Sym

public section

/-- **An instruction is sound**: from a state `S` describes, Kraken's semantics of `op` ends in a
state the symbolic step's `S'` describes, at the pc its exit says. -/
@[expose] def OpOk [Labels] (env : Env) {w : RegWidth} (op : Operation w) : Prop :=
  ∀ (S S' : SState) (x : Exit) (m : MachineData) (p : Std.Rco Int64), env.WF → Match env S m →
    stepOp op S = some (S', x) →
    (op.interp p m (fun m' => .done ⟨m', p.upper⟩) (fun a m' => .done ⟨m', a⟩)).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st)

/-- A step that falls through to a state matching `m'`. -/
theorem done_fall [Labels] {env : Env} {S' : SState} {m' : MachineData} {p : Std.Rco Int64}
    (h : Match env S' m') :
    (Effects.done ⟨m', p.upper⟩).All (fun st => Match env S' st.data ∧ PcOk env .fall p.upper st) :=
  ⟨h, rfl⟩

theorem shiftW_eq {w : RegWidth} (e : ShiftRegExpr w) (regs : Reg64s) (p : Std.Rco Int64) :
    e.interp regs p = shiftW e.shift (regs.getRegOrZr e.reg) e.amount.toInt.toNat := by
  unfold ShiftRegExpr.interp shiftW
  cases e.shift <;> rfl

theorem ofInt_toInt64 (a : Int64) : BitVec.ofInt 64 a.toInt = a.toBitVec := by
  rw [Int64.toInt, BitVec.ofInt_toInt]

theorem lo12_val (x : BitVec 64) :
    (Int64.ofNat (x &&& 0xFFF#64).toNat).toBitVec = x &&& 0xFFF#64 := by
  rw [Int64.toBitVec_ofNat', BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- The address of an `ADRP` or `:lo12:` operand (`labelAddr`) is the operand's value. -/
theorem labelAddr_spec {t : ConstExpr} {x : Sym} (h : labelAddr t = some x) (p : Std.Rco Int64) :
    (t.interp p).toBitVec = x.eval env := by
  unfold labelAddr at h
  split at h
  · cases h
    rfl
  · cases h
    simp only [ConstExpr.interp, Int64.toBitVec_add, Sym.eval, BinOp.apply, low_W64, ext_W64,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · cases h

theorem Match.shiftOp (hm : Match env S m) {w : RegWidth} {e : ShiftRegExpr w} {b : Sym}
    (h : S.shiftOp e = some b) (p : Std.Rco Int64) : e.interp m.regs p = low w (b.eval env) := by
  unfold SState.shiftOp at h
  cases ha : S.getZr e.reg with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    cases h
    rw [shiftW_eq, hm.getZr ha, eval_mkUn]
    simp only [UnOp.apply, low_ext]

theorem Match.extOrImm (hm : Match env S m) {w : RegWidth} {e : ExtOrImmReg} {b : Sym}
    (h : S.extOrImm w e = some b) (p : Std.Rco Int64) :
    (e.interp m.regs p : w.type) = low w (b.eval env) := by
  cases e with
  | ext e =>
    change (do let a ← S.getZr64 e.reg.reg.base; some (mkUn (.extend e.ext) w a)) = some b at h
    cases ha : S.getZr64 e.reg.reg.base with
    | none => rw [ha] at h; cases h
    | some a =>
      rw [ha] at h
      cases h
      rw [eval_mkUn]
      simp only [ExtOrImmReg.interp, ExtRegExpr.interp, hm.getZr64 ha, UnOp.apply, low_ext]
  | imm i =>
    obtain ⟨c, sh⟩ := i
    change immSym w c sh = some b at h
    cases c with
    | int64 k =>
      cases sh with
      | S0 =>
        cases h
        simp only [ExtOrImmReg.interp, ConstExpr.interp, eval_lit_toNat, low_ext]
      | S12 =>
        cases h
        simp only [ExtOrImmReg.interp, ConstExpr.interp, eval_lit_toNat, low_ext]
    | lo12 c' =>
      cases sh with
      | S0 =>
        cases w with
        | W32 => cases h
        | W64 =>
          cases hx : labelAddr c' with
          | none => simp only [immSym, hx, reduceCtorEq] at h
          | some x =>
            simp only [immSym, hx, Option.some.injEq] at h
            subst h
            simp only [ExtOrImmReg.interp, ConstExpr.interp, Sym.eval, BinOp.apply, low_W64,
              ext_W64, ofInt_toInt64, lo12_val, labelAddr_spec (env := env) hx p]
      | S12 => cases h
    | _ => cases sh <;> cases h

theorem logicImm_spec {w : RegWidth} {c : ConstExpr} {b : Sym} (h : logicImm w c = some b)
    (p : Std.Rco Int64) :
    BitVec.ofInt w.bits (c.interp p).toInt = low w (b.eval env) := by
  unfold logicImm at h
  split at h
  · cases h
    simp only [ConstExpr.interp, eval_lit_toNat, low_ext]
  · cases h

theorem target_spec {t : ConstExpr} {l : Label} (h : target t = some l) (p : Std.Rco Int64) :
    t.evalBranchTarget p = Labels.label l := by
  cases t <;> cases h
  rfl

/-! ## Values of loads and stores -/

omit [Labels] in
theorem ext_ofInt_toNat (w : RegWidth) (x : BitVec 64) (h : x.toNat < 2 ^ (8 * (w : MemWidth).bytes)) :
    ext w (BitVec.ofInt (w : MemWidth).bits (x.toNat : Int)) = x := by
  cases w
  · show (BitVec.ofInt 32 (x.toNat : Int)).setWidth 64 = x
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    change x.toNat < 2 ^ 32 at h
    omega
  · show BitVec.ofInt 64 (x.toNat : Int) = x
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

omit [Labels] in
theorem ext_ofInt_toNat_narrow (k : Nat) (hk : k ≤ 32) (x : BitVec 64) (h : x.toNat < 2 ^ k) :
    ext .W32 ((BitVec.ofInt k (x.toNat : Int)).zeroExtend 32) = x := by
  show ((BitVec.ofInt k (x.toNat : Int)).setWidth 32).setWidth 64 = x
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hk
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

omit [Labels] in
theorem low_eq_setWidth (w : RegWidth) (x : BitVec 64) : low w x = x.setWidth w.bits := by
  cases w
  · exact low_W32 x
  · rw [low_W64, BitVec.setWidth_eq]

omit [Labels] in
/-- The bytes Kraken stores for a register of width `w`. -/
theorem store_bytes (w : RegWidth) (x : BitVec 64) :
    ∀ t < (w : MemWidth).bytes, (Int.toBytes (w : MemWidth).bytes (low w x).toInt)[t]? =
      some (byteOf x t) := by
  intro t ht
  rw [low_eq_setWidth]
  cases w
  · exact toBytes_setWidth x 4 t ht
  · exact toBytes_setWidth x 8 t ht

omit [Labels] in
/-- The bytes Kraken stores for the low `8 * n` bits of a 32-bit register (`STRB`, `STRH`). -/
theorem store_bytes_narrow (n : Nat) (hn : n ≤ 4) (x : BitVec 64) :
    ∀ t < n, (Int.toBytes n ((low .W32 x).take (8 * n)).toInt)[t]? = some (byteOf x t) := by
  intro t ht
  have : (low .W32 x).take (8 * n) = x.setWidth (8 * n) := by
    rw [low_W32, BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by show 8 * n ≤ 32; omega),
      BitVec.setWidth_setWidth_of_le _ (by show 8 * n ≤ 32; omega)]
  rw [this]
  exact toBytes_setWidth x n t ht

end

end NativeRustcArm.Sym
