import Rv64Verifier.Machine
import RiscvZkvm.Rv64.SailEquiv.ALUProofs

/-!
# The word operations agree with Sail

For every `WordOp` and `ShiftOp`, running Sail's `execute_*` from a related state retires and
reaches a state related to what `step` gives, the same statement riscv-zkvm proves for its own
instructions (`addiw_sail_equiv`).
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64 RiscvZkvm.Rv64.SailEquiv RiscvZkvm.Sail.Functions Sail

/-- What `step` does on `.word op rd rs1 rs2`. -/
def wordStep (op : WordOp) (rd rs1 rs2 : Reg) (s : MachineState) : MachineState :=
  (s.setReg rd ((wordResult op ((s.getReg rs1).truncate 32) ((s.getReg rs2).truncate 32)).signExtend 64)).setPC
    (s.pc + 4)

/-- What `step` does on `.shiftw op rd rs1 shamt`. -/
def shiftStep (op : ShiftOp) (rd rs1 : Reg) (shamt : BitVec 5) (s : MachineState) : MachineState :=
  (s.setReg rd ((shiftResult op ((s.getReg rs1).truncate 32) shamt).signExtend 64)).setPC (s.pc + 4)

theorem step_word {code : Code} {s : MachineState} {op : WordOp} {rd rs1 rs2 : Reg}
    (h : code.fetch s.pc = some (.word op rd rs1 rs2)) : step code s = some (wordStep op rd rs1 rs2 s) := by
  simp [step, h, wordStep]

theorem step_shiftw {code : Code} {s : MachineState} {op : ShiftOp} {rd rs1 : Reg} {shamt : BitVec 5}
    (h : code.fetch s.pc = some (.shiftw op rd rs1 shamt)) : step code s = some (shiftStep op rd rs1 shamt s) := by
  simp [step, h, shiftStep]

/-- Sail's instruction for a word operation (`OP-32`). -/
def sailWord (op : WordOp) (rd rs1 rs2 : regidx) : SailM ExecutionResult :=
  match op with
  | .add => execute_RTYPEW rs2 rs1 rd .ADDW
  | .sub => execute_RTYPEW rs2 rs1 rd .SUBW
  | .sll => execute_RTYPEW rs2 rs1 rd .SLLW
  | .srl => execute_RTYPEW rs2 rs1 rd .SRLW
  | .sra => execute_RTYPEW rs2 rs1 rd .SRAW
  | .mul => execute_MULW rs2 rs1 rd
  | .div => execute_DIVW rs2 rs1 rd false
  | .divu => execute_DIVW rs2 rs1 rd true
  | .rem => execute_REMW rs2 rs1 rd false
  | .remu => execute_REMW rs2 rs1 rd true

/-- Sail's instruction for a 32-bit immediate shift. -/
def sailShift (op : ShiftOp) (rd rs1 : regidx) (shamt : BitVec 5) : SailM ExecutionResult :=
  match op with
  | .sll => execute_SHIFTIWOP shamt rs1 rd .SLLIW
  | .srl => execute_SHIFTIWOP shamt rs1 rd .SRLIW
  | .sra => execute_SHIFTIWOP shamt rs1 rd .SRAIW

private theorem extractLsb_31 (x : BitVec 64) : Sail.BitVec.extractLsb x 31 0 = x.truncate 32 := by
  apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.extractLsb]

private theorem extractLsb_4 (b : BitVec 32) : (Sail.BitVec.extractLsb b 4 0).toNat = b.toNat % 32 := by
  simp [Sail.BitVec.extractLsb]

private theorem sign_extend_32 (v : BitVec 32) : sign_extend (m := 64) v = v.signExtend 64 := rfl

private theorem to_bits_truncate_32 (x : Int) : to_bits_truncate (l := 32) x = BitVec.ofInt 32 x := by
  simp [to_bits_truncate, get_slice_int]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega

private theorem toInt_eq_zero_32 (b : BitVec 32) : b.toInt = 0 ↔ b = 0 := by
  constructor
  · intro h; exact BitVec.toInt_inj.mp (by simpa using h)
  · rintro rfl; simp

private theorem toNatInt_eq_zero_32 (b : BitVec 32) : Sail.BitVec.toNatInt b = 0 ↔ b = 0 := by
  simp [Sail.BitVec.toNatInt, BitVec.toNat_eq]

private theorem write_eq {s : SailState} {rd : Reg} {v w : BitVec 64} (h : v = w) :
    some (RETIRE_SUCCESS, sailStateWithReg s rd v) = some (RETIRE_SUCCESS, sailStateWithReg s rd w) := by
  rw [h]

theorem runSail_word {sRv : MachineState} {sSail : SailState} (hrel : StateRel sRv sSail) (op : WordOp)
    (rd rs1 rs2 : Reg) :
    runSail (sailWord op (regToRegidx rd) (regToRegidx rs1) (regToRegidx rs2)) sSail =
      some (RETIRE_SUCCESS, sailStateWithReg sSail rd
        ((wordResult op ((sRv.getReg rs1).truncate 32) ((sRv.getReg rs2).truncate 32)).signExtend 64)) := by
  cases op <;>
    simp only [sailWord, execute_RTYPEW, execute_MULW, execute_DIVW, execute_REMW, runSail_bind,
      runSail_rX_bits_of_stateRel hrel, runSail_pure, runSail_wX_bits_of_reg] <;>
    refine write_eq ?_ <;>
    simp only [extractLsb_31, sign_extend_32, wordResult] <;>
    generalize (sRv.getReg rs1).truncate 32 = a <;> generalize (sRv.getReg rs2).truncate 32 = b <;>
    congr 1
  case mul =>
    rw [to_bits_truncate_32]; apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_mul]
  case div =>
    simp only [Bool.false_eq_true, ite_false, RiscvZkvm.Sail.Functions.not, Bool.not_false, Bool.true_and,
      to_bits_truncate_32, beq_iff_eq, toInt_eq_zero_32]
    by_cases hb : b = 0
    · subst hb; simp <;> decide
    · have key : BitVec.ofInt 32 (a.toInt.tdiv b.toInt) = a.sdiv b := by
        apply BitVec.eq_of_toInt_eq; rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]
      simp only [hb, ite_false, decide_eq_true_eq]
      split
      · have h1 := Int.natAbs_tdiv_le_natAbs a.toInt b.toInt
        have h2 := @BitVec.toInt_lt 32 a
        have h3 := @BitVec.le_toInt 32 a
        have hq : a.toInt.tdiv b.toInt = 2 ^ 31 := by omega
        rw [← key, hq]; decide
      · exact key
  case divu =>
    simp only [RiscvZkvm.Sail.Functions.not, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_true,
      ite_false, to_bits_truncate_32, beq_iff_eq, toNatInt_eq_zero_32]
    by_cases hb : b = 0
    · subst hb; simp <;> decide
    · simp only [hb, ite_false, Sail.BitVec.toNatInt]
      apply BitVec.eq_of_toNat_eq
      have := Nat.div_le_self a.toNat b.toNat
      have := a.isLt
      simp [BitVec.toNat_ofInt, BitVec.toNat_udiv]
      rw [← Int.natCast_ediv]
      generalize a.toNat / b.toNat = q at *
      omega
  case rem =>
    simp only [Bool.false_eq_true, ite_false, to_bits_truncate_32, beq_iff_eq, toInt_eq_zero_32]
    by_cases hb : b = 0
    · simp only [hb, ite_true, BitVec.ofInt_toInt]
    · simp only [hb, ite_false, ← BitVec.toInt_srem, BitVec.ofInt_toInt]
  case remu =>
    simp only [ite_true, to_bits_truncate_32, beq_iff_eq, toNatInt_eq_zero_32]
    by_cases hb : b = 0
    · simp only [hb, ite_true, Sail.BitVec.toNatInt]
      apply BitVec.eq_of_toNat_eq
      simp
    · simp only [hb, ite_false, Sail.BitVec.toNatInt]
      apply BitVec.eq_of_toNat_eq
      have : a.toNat % b.toNat < b.toNat := Nat.mod_lt _ (Nat.pos_of_ne_zero (by simpa [BitVec.toNat_eq] using hb))
      have := b.isLt
      simp [BitVec.toNat_ofInt, BitVec.toNat_umod]
      rw [← Int.ofNat_tmod]
      omega

theorem runSail_shift {sRv : MachineState} {sSail : SailState} (hrel : StateRel sRv sSail) (op : ShiftOp)
    (rd rs1 : Reg) (shamt : BitVec 5) :
    runSail (sailShift op (regToRegidx rd) (regToRegidx rs1) shamt) sSail =
      some (RETIRE_SUCCESS, sailStateWithReg sSail rd
        ((shiftResult op ((sRv.getReg rs1).truncate 32) shamt).signExtend 64)) := by
  cases op <;>
    simp only [sailShift, execute_SHIFTIWOP, runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
      runSail_wX_bits_of_reg] <;>
    refine write_eq ?_ <;>
    simp only [extractLsb_31, sign_extend_32, shiftResult] <;>
    congr 1

/-- Writing `rd` and moving on: Sail's register write is related to riscv-zkvm's. -/
private theorem write_rd_equiv {sRv : MachineState} {sSail : SailState} (hrel : StateRel sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4)) (rd : Reg) (v : BitVec 64) :
    StateRel ((sRv.setReg rd v).setPC (sRv.pc + 4)) (sailStateWithReg sSail rd v) ∧
      (sailStateWithReg sSail rd v).regs.get? Register.nextPC = some (sRv.pc + 4) ∧
      PlatformFrame sSail (sailStateWithReg sSail rd v) :=
  ⟨⟨reg_agree_after_insert sSail sRv hrel rd v,
    fun a ha => by simpa [MachineState.setPC, MachineState.getMem] using hrel.mem_agree a ha⟩,
    by simp [h_nextpc], platformFrame_sailStateWithReg _ _ _⟩

theorem wordOp_sail_equiv (op : WordOp) (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4)) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (sailWord op (regToRegidx rd) (regToRegidx rs1) (regToRegidx rs2)) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (wordStep op rd rs1 rs2 sRv) sSail' ∧
      sSail'.regs.get? Register.nextPC = some (sRv.pc + 4) ∧
      PlatformFrame sSail sSail' :=
  ⟨_, runSail_word hrel op rd rs1 rs2, write_rd_equiv hrel h_nextpc rd _⟩

theorem shiftOp_sail_equiv (op : ShiftOp) (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4)) (rd rs1 : Reg) (shamt : BitVec 5) :
    ∃ sSail',
      runSail (sailShift op (regToRegidx rd) (regToRegidx rs1) shamt) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (shiftStep op rd rs1 shamt sRv) sSail' ∧
      sSail'.regs.get? Register.nextPC = some (sRv.pc + 4) ∧
      PlatformFrame sSail sSail' :=
  ⟨_, runSail_shift hrel op rd rs1 shamt, write_rd_equiv hrel h_nextpc rd _⟩

end Rv64Verifier
