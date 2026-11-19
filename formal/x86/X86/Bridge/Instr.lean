module

public import X86.Bridge.Basic

/-!
# The instruction bridge

Each `QInstr` does on Kraken's machine what `QInstr.step` says (`QInstr.toInstr_correct`), and each
condition's flag-setting instruction leaves the state related and sets the flags so that `Cond.cc`
holds exactly when the condition does (`Cond.toInstr_correct`). Both hold for every choice Kraken
leaves undefined (`Effects.All`), such as the AF flag of `xor`.
-/

public section

namespace X86

variable [Labels]

/-! ## Operands -/

theorem imm8_count (n : Nat) (m : MachineData) (p : Std.Rco Int64) :
    (ShiftCountExpr.imm8 (.int64 (Int64.ofNat n))).interpMasked m p .W64 = n % 64 := by
  simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp, BitVec.take,
    BitVec.extractLsb'_toNat, Int64.toBitVec_ofNat']
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem cl_count {s : QState} {m : MachineData} (hr : StateRel s m) (p : Std.Rco Int64) :
    ShiftCountExpr.cl.interpMasked m p .W64 = (s.reg .rcx).toNat % 64 := by
  have h := hr.1 .rcx
  simp only [Reg64s.get64] at h
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take, h]
  simp [BitVec.extractLsb'_toNat]
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

omit [Labels] in
theorem imm_trunc (k : Int64) : k.toBitVec.truncate 64 = k.toUInt64.toBitVec := by
  simp only [BitVec.truncate, BitVec.setWidth_eq, Int64.toBitVec_toUInt64]

/-! ## Instructions -/

omit [Labels] in
theorem shl_val (x : UInt64) (n : Nat) :
    (x <<< n.toUInt64).toBitVec = x.toBitVec <<< (n % 64) := by
  simp [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]

omit [Labels] in
theorem shr_val (x : UInt64) (n : Nat) :
    (x >>> n.toUInt64).toBitVec = x.toBitVec.ushiftRight (n % 64) := by
  simp [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]

omit [Labels] in
theorem shlcl_val (x c : UInt64) :
    (x <<< (c &&& 63)).toBitVec = x.toBitVec <<< (c.toNat % 64) := by
  simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']
  congr 1
  simp [BitVec.toNat_umod]
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The leaves of a shift: every branch on the count and on Kraken's undefined flags. -/
local macro "kleaves" t:term : tactic => `(tactic| (
  repeat' (first | intro _ | split | simp only [Effects.All])
  all_goals exact ⟨by trivial, $t⟩))

/-- The unfolding of an instruction down to its operands. -/
local macro "kunfold" hr:term : tactic => `(tactic|
  simp only [QInstr.toInstr, Cond.toInstr, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, StateRel.get $hr, imm_trunc, MachineData.set, Effects.All])

/-- An instruction run from a related state ends at the next address in a state related to the one
`QInstr.step` gives, whatever Kraken leaves undefined. -/
theorem QInstr.toInstr_correct (i : QInstr) {s s' : QState} {m : MachineData}
    (h : i.step s = some s') (hr : StateRel s m) (p : Std.Rco Int64) (a : Int64) :
    (Instr.interp i.toInstr m p (fun m' => .done ⟨m', a⟩) (fun t m' => .done ⟨m', t⟩)).All
      (fun st => st.pc = a ∧ StateRel s' st.data) := by
  cases i with
  | mov d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg d _⟩
  | movi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg d _⟩
  | load d ad =>
    simp only [QInstr.step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    kunfold hr
    rw [Addr.interp_eq ad hr p, load_All hr.2 hv]
    exact ⟨rfl, hr.setReg d _⟩
  | store ad r =>
    simp only [QInstr.step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    kunfold hr
    rw [Addr.interp_eq ad hr p, store_All hr.2 hv]
    exact ⟨rfl, hr.store hv _⟩
  | storei ad k =>
    simp only [QInstr.step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    kunfold hr
    rw [Addr.interp_eq ad hr p, store_All hr.2 hv]
    exact ⟨rfl, hr.store hv _⟩
  | lea d ad =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (Addr.interp_eq ad hr p)⟩
  | add d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_add, BitVec.add_comm])⟩
  | addi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_add, BitVec.add_comm])⟩
  | sub d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_sub])⟩
  | subi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_sub])⟩
  | xor d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact fun _ => ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_xor])⟩
  | xori d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact fun _ => ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_xor])⟩
  | and d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact fun _ => ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_and])⟩
  | andi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact fun _ => ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_and])⟩
  | or d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact fun _ => ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_or])⟩
  | not d =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_not])⟩
  | neg d =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    exact ⟨trivial, hr.setReg' d (by rw [UInt64.toBitVec_sub]; simp)⟩
  | shli d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    rw [imm8_count]
    split
    · rename_i h0; simp only [beq_iff_eq] at h0
      exact ⟨rfl, hr.setReg' d (by rw [shl_val, h0]; simp)⟩
    · kleaves hr.setReg' d (shl_val _ _).symm
  | shri d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    rw [imm8_count]
    split
    · rename_i h0; simp only [beq_iff_eq] at h0
      exact ⟨rfl, hr.setReg' d (by rw [shr_val, h0]; simp)⟩
    · kleaves hr.setReg' d (shr_val _ _).symm
  | sari d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    rw [imm8_count]
    split
    · rename_i h0; simp only [beq_iff_eq] at h0
      exact ⟨rfl, hr.setReg' d (by rw [h0]; simp)⟩
    · kleaves hr.setReg' d rfl
  | roli d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    rw [imm8_count]
    split
    · rename_i h0; simp only [beq_iff_eq] at h0
      exact ⟨rfl, hr.setReg' d (by
        rw [h0]; simp [BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.ushiftRight_eq_zero])⟩
    · kleaves hr.setReg' d rfl
  | shlcl d =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    kunfold hr
    rw [cl_count hr]
    split
    · rename_i h0; simp only [beq_iff_eq] at h0
      exact ⟨rfl, hr.setReg' d (by rw [shlcl_val, h0]; simp)⟩
    · kleaves hr.setReg' d (shlcl_val _ _).symm

/-! ## Conditions -/

omit [Labels] in
theorem zf_sub (x y : UInt64) : (x.toBitVec - y.toBitVec == BitVec.zero 64) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.zero_eq, BitVec.sub_eq_iff_eq_add,
    BitVec.zero_add, UInt64.toBitVec_inj]
omit [Labels] in
theorem cf_sub (x y : UInt64) :
    (BitVec.unsigned (x.toBitVec - y.toBitVec) != x.toBitVec.unsigned - y.toBitVec.unsigned) =
      decide (x < y) := by
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  simp only [UInt64.size] at hx hy
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, UInt64.lt_iff_toNat_lt]
  simp only [BitVec.unsigned, BitVec.toNat_sub, UInt64.toNat_toBitVec, ne_eq]
  by_cases h : x.toNat < y.toNat
  · simp only [h, iff_true]; omega
  · simp only [h, iff_false, Decidable.not_not]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
omit [Labels] in
theorem zf_and (x y : UInt64) :
    (x.toBitVec &&& y.toBitVec == BitVec.zero 64) = ((x &&& y) == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.zero_eq, ← UInt64.toBitVec_and,
    ← UInt64.toBitVec_inj]
  rfl

/-- A condition's `cmp` or `test` keeps the state related and sets the flags so that `Cond.cc`
holds exactly when the condition does. -/
theorem Cond.toInstr_correct (c : Cond) {s : QState} {m : MachineData} (hr : StateRel s m)
    (p : Std.Rco Int64) (a : Int64) :
    (Instr.interp c.toInstr m p (fun m' => .done ⟨m', a⟩) (fun t m' => .done ⟨m', t⟩)).All
      (fun st => st.pc = a ∧ StateRel s st.data ∧ c.cc.interp st.data.status = c.eval s) := by
  cases c with
  | cmp rel x b =>
    cases b <;> cases rel <;> kunfold hr <;>
      simp only [Rhs.toOperand, ConstExpr.interp, StateRel.get hr, Effects.All, Cond.cc, Cond.eval,
        Rhs.eval, CondCode.interp,
        StatusFlags.from_result, Width.bits, zf_sub, cf_sub] <;>
      refine ⟨trivial, hr, ?_⟩
    all_goals first | trivial | simp [← UInt64.not_lt]
  | test z x b =>
    cases b <;> cases z <;> kunfold hr <;>
      simp only [Rhs.toOperand, ConstExpr.interp, StateRel.get hr, Effects.All, Cond.cc, Cond.eval,
        Rhs.eval, CondCode.interp, StatusFlags.from_result, Width.bits, zf_and] <;>
      intro _ <;> refine ⟨trivial, hr, ?_⟩
    all_goals (generalize (_ == (0 : UInt64)) = t; cases t <;> rfl)

end X86
