module

public import NativeArm.Instr

/-!
# Running straight-line AArch64 code

`Runs is m Q`: the instructions `is`, run from `m` one after the other, each falling through to the
next, end in a state satisfying `Q`, whatever Kraken leaves undefined. One lemma per instruction
form the compiler emits gives the state after it, so that a proof about a QM instruction's code
steps through it without unfolding Kraken's instruction semantics.
-/

open Native

namespace NativeArm

@[expose] public section

/-- `is` run from `m`, each instruction falling through, ends in a state satisfying `Q`. -/
def Runs [Labels] : List Instr → MachineData → (MachineData → Prop) → Prop
  | [], m, Q => Q m
  | i :: is, m, Q => ∀ p a,
    (i.interp m p (fun m' => .done ⟨m', a⟩) (fun t m' => .done ⟨m', t⟩)).All
      (fun st => st.pc = a ∧ Runs is st.data Q)

end

public section

variable [Labels] {is js : List Instr} {m : MachineData} {Q Q' : MachineData → Prop}

theorem Runs.nil (h : Q m) : Runs [] m Q := h

theorem Runs.mono (hQ : ∀ m, Q m → Q' m) (h : Runs is m Q) : Runs is m Q' := by
  induction is generalizing m with
  | nil => exact hQ _ h
  | cons i is ih => exact fun p a => Effects.All.mono (fun _ h => ⟨h.1, ih h.2⟩) (h p a)

theorem Runs.append (h : Runs is m (fun m' => Runs js m' Q)) : Runs (is ++ js) m Q := by
  induction is generalizing m with
  | nil => exact h
  | cons i is ih => exact fun p a => Effects.All.mono (fun _ h => ⟨h.1, ih h.2⟩) (h p a)

/-- An instruction that leads to `m'` and falls through. -/
theorem Runs.step {i : Instr} {m' : MachineData}
    (hi : ∀ p (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
      i.interp m p next jmp = .require_exec_access p (fun _ => next m'))
    (h : Runs is m' Q) : Runs (i :: is) m Q := by
  intro p a
  rw [hi]
  exact ⟨rfl, h⟩

/-- The value of a shifted register operand. -/
abbrev sval (m : MachineData) (e : ShiftRegExpr .W64) : BitVec 64 := e.interp m.regs ⟨0, 0⟩

/-! ## Data processing -/

variable {d : XReg} {a : RegOrZr .W64} {e : ShiftRegExpr .W64}

theorem Runs.orr (h : Runs is (m.setX d (m.regs.getRegOrZr a ||| sval m e)) Q) :
    Runs (⟨.W64, .ORR_s (xr d) a e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.orn (h : Runs is (m.setX d (m.regs.getRegOrZr a ||| ~~~sval m e)) Q) :
    Runs (⟨.W64, .ORN_s (xr d) a e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.eor (h : Runs is (m.setX d (m.regs.getRegOrZr a ^^^ sval m e)) Q) :
    Runs (⟨.W64, .EOR_s (xr d) a e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.and (h : Runs is (m.setX d (m.regs.getRegOrZr a &&& sval m e)) Q) :
    Runs (⟨.W64, .AND_s (xr d) a e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.add (h : Runs is (m.setX d (m.regs.getRegOrZr a + sval m e)) Q) :
    Runs (⟨.W64, .ADD_s (xr d) a e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.sub (h : Runs is (m.setX d (m.regs.getRegOrZr a - sval m e)) Q) :
    Runs (⟨.W64, .SUB_s (xr d) a e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.addi {b : XReg} {k : Int64}
    (h : Runs is (m.setX d ((m.regs.getXReg b).toBitVec + k.toBitVec)) Q) :
    Runs (⟨.W64, .ADD_e (xs d) (xs b) (.imm { imm := .int64 k, shift := .S0 })⟩ :: is) m Q := by
  refine Runs.step (m' := m.setX d ((m.regs.getXReg b).toBitVec + k.toBitVec))
    (fun p next jmp => ?_) h
  simp only [Instr.interp, Operation.interp, ExtOrImmReg.interp, ConstExpr.interp,
    MachineData.setRegOrSp, getRegOrSp_xs, RegWidth.bits, MemWidth.bits, ofInt_toInt64]
  rfl

theorem Runs.subi {b : XReg} {k : Int64}
    (h : Runs is (m.setX d ((m.regs.getXReg b).toBitVec - k.toBitVec)) Q) :
    Runs (⟨.W64, .SUB_e (xs d) (xs b) (.imm { imm := .int64 k, shift := .S0 })⟩ :: is) m Q := by
  refine Runs.step (m' := m.setX d ((m.regs.getXReg b).toBitVec - k.toBitVec))
    (fun p next jmp => ?_) h
  simp only [Instr.interp, Operation.interp, ExtOrImmReg.interp, ConstExpr.interp,
    MachineData.setRegOrSp, getRegOrSp_xs, RegWidth.bits, MemWidth.bits, ofInt_toInt64]
  rfl

theorem Runs.lslv {b c : XReg}
    (h : Runs is (m.setX d ((m.regs.getXReg b).toBitVec <<< ((m.regs.getXReg c).toNat % 64))) Q) :
    Runs (⟨.W64, .LSLV (xr d) (xr b) (xr c)⟩ :: is) m Q := by
  refine Runs.step (fun p next jmp => ?_) h
  simp only [Instr.interp, Operation.interp, MachineData.setRegOrZr, getRegOrZr_xr, RegWidth.bits,
    MemWidth.bits, UInt64.toNat_toBitVec]
  rfl

/-! ## Moves of immediates -/

theorem Runs.movz {c : Int64}
    (h : Runs is (m.setX d (BitVec.ofInt 64 c.toInt &&& 0xFFFF#64)) Q) :
    Runs (⟨.W64, .MOVZ (xr d) (.int64 c) .LSL0⟩ :: is) m Q := by
  refine Runs.step (fun p next jmp => ?_) h
  simp only [Instr.interp, Operation.interp, ConstExpr.interp, MachineData.setRegOrZr,
    MovShift.toNat, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits]
  rfl

theorem Runs.movn {c : Int64}
    (h : Runs is (m.setX d (~~~(BitVec.ofInt 64 c.toInt &&& 0xFFFF#64))) Q) :
    Runs (⟨.W64, .MOVN (xr d) (.int64 c) .LSL0⟩ :: is) m Q := by
  refine Runs.step (fun p next jmp => ?_) h
  simp only [Instr.interp, Operation.interp, ConstExpr.interp, MachineData.setRegOrZr,
    MovShift.toNat, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits]
  rfl

theorem Runs.movk {c : Nat} {s : MovShift .W64}
    (h : Runs is (m.setX d (((m.regs.getXReg d).toBitVec &&& ~~~(0xFFFF#64 <<< s.toNat)) |||
      ((BitVec.ofInt 64 (Int64.ofNat c).toInt &&& 0xFFFF#64) <<< s.toNat))) Q) :
    Runs (movk d c s :: is) m Q := by
  refine Runs.step (fun p next jmp => ?_) h
  simp only [NativeArm.movk, Instr.interp, Operation.interp, ConstExpr.interp,
    MachineData.setRegOrZr,
    getRegOrZr_xr, RegWidth.bits, MemWidth.bits]
  rfl

/-! ## Flags -/

theorem Runs.subs {b : XReg}
    (h : Runs is { m with status := (StatusFlags.subs (m.regs.getRegOrZr (xr b) - sval m e)
      (m.regs.getRegOrZr (xr b)) (sval m e)) } Q) :
    Runs (⟨.W64, .SUBS_s xzr (xr b) e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

theorem Runs.subsi {b : XReg} {k : Int64}
    (h : Runs is { m with status := (StatusFlags.subs ((m.regs.getXReg b).toBitVec - k.toBitVec)
      (m.regs.getXReg b).toBitVec k.toBitVec) } Q) :
    Runs (⟨.W64, .SUBS_e xzr (xs b) (.imm { imm := .int64 k, shift := .S0 })⟩ :: is) m Q := by
  refine Runs.step (fun p next jmp => ?_) h
  simp only [Instr.interp, Operation.interp, ExtOrImmReg.interp, ConstExpr.interp,
    MachineData.setRegOrZr, getRegOrSp_xs, RegWidth.bits, MemWidth.bits, ofInt_toInt64]
  rfl

theorem Runs.ands {b : XReg}
    (h : Runs is { m with status := (StatusFlags.from_result
      (m.regs.getRegOrZr (xr b) &&& sval m e) { c := false, v := false }) } Q) :
    Runs (⟨.W64, .ANDS_s xzr (xr b) e⟩ :: is) m Q := Runs.step (fun _ _ _ => rfl) h

/-! ## Memory -/

theorem AddrExpr.eval_imm (b : XReg) (k : Int64) (m : MachineData) (p : Std.Rco Int64) :
    AddrExpr.eval (immOp b k) m p =
      ((m.regs.getXReg b).toBitVec + k.toBitVec, m) := by
  simp only [AddrExpr.eval, ConstExpr.interp, getRegOrSp_xs, BitVec.signed, BitVec.ofInt_add,
    BitVec.ofInt_toInt, ofInt_toInt64]

theorem AddrExpr.eval_reg (b c : XReg) (m : MachineData) (p : Std.Rco Int64) :
    AddrExpr.eval (regOp b c) m p =
      ((m.regs.getXReg b).toBitVec + (m.regs.getXReg c).toBitVec, m) := by
  simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend, getRegOrSp_xs,
    BitVec.signed, BitVec.unsigned, BitVec.ofInt_add, BitVec.ofInt_toInt, RegOrZr.base,
    Reg64s.getRegOrZr64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Runs.ldr {d : XReg} {ae : AddrExpr} {q : UInt64 → Option UInt64} {ad v : UInt64}
    (hc : ∀ ok, ae.checkSPAlignment m ok = ok ()) (he : ∀ p, ae.eval m p = (ad.toBitVec, m))
    (hm : MemRel q m.dmem) (hv : q ad = some v) (h : Runs is (m.setX d v.toBitVec) Q) :
    Runs (⟨.W64, .LDR (xr d) (.addr ae)⟩ :: is) m Q := by
  intro p a
  simp only [Instr.interp, Operation.interp, AddrOrLit.interpLoad, AddrExpr.interpLoad, hc, he,
    Effects.All]
  rw [load_All hm hv]
  exact ⟨rfl, h⟩

theorem Runs.str {ae : AddrExpr} {src : RegOrZr .W64} {q : UInt64 → Option UInt64}
    {ad v : UInt64}
    (hc : ∀ ok, ae.checkSPAlignment m ok = ok ()) (he : ∀ p, ae.eval m p = (ad.toBitVec, m))
    (hm : MemRel q m.dmem) (hv : q ad = some v)
    (h : Runs is
      { m with dmem := Mem.storeInt m.dmem ad.toBitVec 8 (m.regs.getRegOrZr src).toInt } Q) :
    Runs (⟨.W64, .STR src ae⟩ :: is) m Q := by
  intro p a
  simp only [Instr.interp, Operation.interp, AddrExpr.interpStore, hc, he, Effects.All]
  rw [store_All hm hv]
  exact ⟨rfl, h⟩

end

end NativeArm
