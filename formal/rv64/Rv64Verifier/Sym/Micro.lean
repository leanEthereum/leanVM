import Rv64Verifier.Sym.Expr

/-!
# Micro-operations

Ported from sig.golf's `SigGolfCandidate.Rv`.

Every supported `Instruction` is classified into one of six micro-operation shapes (`Micro`).
`classify_sound` proves that one machine step (`Rv64Verifier.step`, which runs riscv-zkvm's
`RiscvZkvm.Rv64.step` on a base instruction) agrees with the much smaller micro-semantics
`Micro.exec`, up to the state's code map, which a base step replaces by `code.baseMap`. The
symbolic executor only has to be proven sound for `Micro`.
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

/-- ALU operand. -/
inductive Src where
  | reg (r : Reg)
  | imm (v : Word)
  | pc
  deriving Repr

def Src.eval (s : MachineState) : Src → Word
  | .reg r => s.getReg r
  | .imm v => v
  | .pc => s.pc

inductive Micro where
  | alu (rd : Reg) (op : BinOp) (a b : Src)
  | load (k : LoadKind) (rd rs : Reg) (off : Word)
  | store (k : StoreKind) (rs1 rs2 : Reg) (off : Word)
  | branch (op : CmpOp) (rs1 rs2 : Reg) (off : Word)
  | jal (rd : Reg) (off : Word)
  | jalr (rd rs : Reg) (off : Word)
  deriving Repr

def LoadKind.read (s : MachineState) (addr : Word) : LoadKind → Word
  | .d => s.getMem addr
  | .w => (s.getWord32 addr).signExtend 64
  | .wu => (s.getWord32 addr).zeroExtend 64
  | .h => (s.getHalfword addr).signExtend 64
  | .hu => (s.getHalfword addr).zeroExtend 64
  | .b => (s.getByte addr).signExtend 64
  | .bu => (s.getByte addr).zeroExtend 64

def StoreKind.write (s : MachineState) (addr v : Word) : StoreKind → MachineState
  | .d => s.setMem addr v
  | .w => s.setWord32 addr (v.truncate 32)
  | .h => s.setHalfword addr (v.truncate 16)
  | .b => s.setByte addr (v.truncate 8)

theorem LoadKind.read_sub (s : MachineState) (addr : Word) (k : LoadKind) (hk : k ≠ .d) :
    k.read s addr = k.fromWord (s.getMem (alignToDword addr)) (byteOffset addr) := by
  cases k <;> first | exact absurd rfl hk | rfl

theorem StoreKind.write_sub (s : MachineState) (addr v : Word) (k : StoreKind) (hk : k ≠ .d) :
    k.write s addr v =
      s.setMem (alignToDword addr) (k.merge (s.getMem (alignToDword addr)) (byteOffset addr) v) := by
  cases k <;> first | exact absurd rfl hk | rfl

/-- Concrete semantics of micro-operations. -/
def Micro.exec (s : MachineState) : Micro → Option MachineState
  | .alu rd op a b => some ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4))
  | .load k rd rs off =>
    if validAccess k.width (s.getReg rs + off) then
      some ((s.setReg rd (k.read s (s.getReg rs + off))).setPC (s.pc + 4))
    else none
  | .store k rs1 rs2 off =>
    if validAccess k.width (s.getReg rs1 + off) then
      some ((k.write s (s.getReg rs1 + off) (s.getReg rs2)).setPC (s.pc + 4))
    else none
  | .branch op rs1 rs2 off =>
    some (s.setPC (if op.eval (s.getReg rs1) (s.getReg rs2) then s.pc + off else s.pc + 4))
  | .jal rd off => some ((s.setReg rd (s.pc + 4)).setPC (s.pc + off))
  | .jalr rd rs off => some ((s.setReg rd (s.pc + 4)).setPC ((s.getReg rs + off) &&& ~~~1#64))

def luiVal (imm : BitVec 20) : Word := ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64

def shiftWordOp : ShiftOp → WordOp
  | .sll => .sll
  | .srl => .srl
  | .sra => .sra

/-- Classify an instruction. `none` is unsupported (`ECALL`, `EBREAK`, `CSRS`, and the
pseudo-instructions the decoder never produces). -/
def classify : Instruction → Option Micro
  | .base i =>
    match i with
    | .ADD rd a b => some (.alu rd .add (.reg a) (.reg b))
    | .SUB rd a b => some (.alu rd .sub (.reg a) (.reg b))
    | .SLL rd a b => some (.alu rd .sll (.reg a) (.reg b))
    | .SRL rd a b => some (.alu rd .srl (.reg a) (.reg b))
    | .SRA rd a b => some (.alu rd .sra (.reg a) (.reg b))
    | .AND rd a b => some (.alu rd .and (.reg a) (.reg b))
    | .OR rd a b => some (.alu rd .or (.reg a) (.reg b))
    | .XOR rd a b => some (.alu rd .xor (.reg a) (.reg b))
    | .SLT rd a b => some (.alu rd .slt (.reg a) (.reg b))
    | .SLTU rd a b => some (.alu rd .sltu (.reg a) (.reg b))
    | .ADDI rd a imm => some (.alu rd .add (.reg a) (.imm (signExtend12 imm)))
    | .ANDI rd a imm => some (.alu rd .and (.reg a) (.imm (signExtend12 imm)))
    | .ORI rd a imm => some (.alu rd .or (.reg a) (.imm (signExtend12 imm)))
    | .XORI rd a imm => some (.alu rd .xor (.reg a) (.imm (signExtend12 imm)))
    | .SLTI rd a imm => some (.alu rd .slt (.reg a) (.imm (signExtend12 imm)))
    | .SLTIU rd a imm => some (.alu rd .sltu (.reg a) (.imm (signExtend12 imm)))
    | .SLLI rd a sh => some (.alu rd .sll (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRLI rd a sh => some (.alu rd .srl (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRAI rd a sh => some (.alu rd .sra (.reg a) (.imm (sh.zeroExtend 64)))
    | .LUI rd imm => some (.alu rd .add (.imm (luiVal imm)) (.imm 0))
    | .AUIPC rd imm => some (.alu rd .add .pc (.imm (luiVal imm)))
    | .LD rd a off => some (.load .d rd a (signExtend12 off))
    | .LW rd a off => some (.load .w rd a (signExtend12 off))
    | .LWU rd a off => some (.load .wu rd a (signExtend12 off))
    | .LH rd a off => some (.load .h rd a (signExtend12 off))
    | .LHU rd a off => some (.load .hu rd a (signExtend12 off))
    | .LB rd a off => some (.load .b rd a (signExtend12 off))
    | .LBU rd a off => some (.load .bu rd a (signExtend12 off))
    | .SD a b off => some (.store .d a b (signExtend12 off))
    | .SW a b off => some (.store .w a b (signExtend12 off))
    | .SH a b off => some (.store .h a b (signExtend12 off))
    | .SB a b off => some (.store .b a b (signExtend12 off))
    | .BEQ a b off => some (.branch .eq a b (signExtend13 off))
    | .BNE a b off => some (.branch .ne a b (signExtend13 off))
    | .BLT a b off => some (.branch .lt a b (signExtend13 off))
    | .BGE a b off => some (.branch .ge a b (signExtend13 off))
    | .BLTU a b off => some (.branch .ltu a b (signExtend13 off))
    | .BGEU a b off => some (.branch .geu a b (signExtend13 off))
    | .JAL rd off => some (.jal rd (signExtend21 off))
    | .JALR rd a off => some (.jalr rd a (signExtend12 off))
    | .ADDIW rd a imm => some (.alu rd (.w .add) (.reg a) (.imm (signExtend12 imm)))
    | .MUL rd a b => some (.alu rd .mul (.reg a) (.reg b))
    | .MULH rd a b => some (.alu rd .mulh (.reg a) (.reg b))
    | .MULHSU rd a b => some (.alu rd .mulhsu (.reg a) (.reg b))
    | .MULHU rd a b => some (.alu rd .mulhu (.reg a) (.reg b))
    | .DIV rd a b => some (.alu rd .div (.reg a) (.reg b))
    | .DIVU rd a b => some (.alu rd .divu (.reg a) (.reg b))
    | .REM rd a b => some (.alu rd .rem (.reg a) (.reg b))
    | .REMU rd a b => some (.alu rd .remu (.reg a) (.reg b))
    | .FENCE => some (.alu .x0 .add (.imm 0) (.imm 0))
    | _ => none
  | .word op rd a b => some (.alu rd (.w op) (.reg a) (.reg b))
  | .shiftw op rd a sh => some (.alu rd (.w (shiftWordOp op)) (.reg a) (.imm (sh.zeroExtend 64)))

/-! ## The code map

`Micro.exec` never reads or writes the code map. -/

theorem getReg_withCode (s : MachineState) (c : Word → Option Instr) (r : Reg) :
    ({ s with code := c } : MachineState).getReg r = s.getReg r := by
  cases r <;> rfl

theorem setReg_withCode (s : MachineState) (c : Word → Option Instr) (r : Reg) (v : Word) :
    ({ s with code := c } : MachineState).setReg r v = { s.setReg r v with code := c } := by
  cases r <;> rfl

theorem withCode_eq (t : MachineState) {c : Word → Option Instr} (h : t.code = c) :
    { t with code := c } = t := by
  subst h; rfl

theorem Micro.exec_withCode (s : MachineState) (c : Word → Option Instr) (m : Micro) :
    m.exec { s with code := c } = (m.exec s).map fun t => { t with code := c } := by
  have hsrc : ∀ a : Src, a.eval { s with code := c } = a.eval s := by
    intro a; cases a <;> simp [Src.eval, getReg_withCode]
  cases m with
  | alu rd op a b =>
    simp only [Micro.exec, hsrc, setReg_withCode, Option.map_some]; rfl
  | load k rd rs off =>
    simp only [Micro.exec, getReg_withCode]
    split
    · cases k <;> simp only [LoadKind.read, Option.map_some, setReg_withCode] <;> rfl
    · rfl
  | store k rs1 rs2 off =>
    simp only [Micro.exec, getReg_withCode]
    split
    · cases k <;> rfl
    · rfl
  | branch op rs1 rs2 off =>
    simp only [Micro.exec, getReg_withCode, Option.map_some]; rfl
  | jal rd off =>
    simp only [Micro.exec, setReg_withCode, Option.map_some]; rfl
  | jalr rd rs off =>
    simp only [Micro.exec, setReg_withCode, getReg_withCode, Option.map_some]; rfl

/-! ## Agreement with the machine -/

private theorem toNat_zext6 (sh : BitVec 6) : (sh.zeroExtend 64).toNat % 64 = sh.toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := sh.isLt
  omega

private theorem toNat_trunc_zext5 (sh : BitVec 5) :
    ((sh.zeroExtend 64).truncate 32).toNat % 32 = sh.toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := sh.isLt
  omega

private theorem toNat_mod32 (sh : BitVec 5) : sh.toNat % 32 = sh.toNat := by
  have := sh.isLt; omega

private theorem setPC_ite (s : MachineState) (c : Prop) [Decidable c] (a b : Word) :
    (if c then s.setPC a else s.setPC b) = s.setPC (if c then a else b) := by
  split <;> rfl

set_option maxHeartbeats 1000000 in
/-- riscv-zkvm's `step` agrees with the micro-semantics on every classified base instruction. -/
theorem classify_base_sound {u : MachineState} {i : Instr} {m : Micro}
    (hu : u.code u.pc = some i) (h : classify (.base i) = some m) :
    RiscvZkvm.Rv64.step u = m.exec u := by
  cases i <;> simp only [classify, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [RiscvZkvm.Rv64.step, hu] <;>
    first
      | rfl
      | (refine (show some (execInstrBr u _) = _ from ?_)
         simp only [execInstrBr, Micro.exec, Src.eval, BinOp.eval, CmpOp.eval, toNat_zext6,
           luiVal, setPC_ite]
         try simp only [toNat_mod32]
         try simp
         try congr
         all_goals exact (toNat_mod32 _).symm)

/-- The code map after one step of `i`: a base instruction runs on `code.baseMap`. -/
def codeAfter (code : Code) (s : MachineState) : Instruction → (Word → Option Instr)
  | .base _ => code.baseMap
  | .word .. => s.code
  | .shiftw .. => s.code

theorem shiftResult_eq (op : ShiftOp) (x : BitVec 32) (sh : BitVec 5) :
    shiftResult op x sh = wordResult (shiftWordOp op) x ((sh.zeroExtend 64).truncate 32) := by
  cases op <;> simp only [shiftResult, wordResult, shiftWordOp, toNat_trunc_zext5]

theorem step_base {code : Code} {s : MachineState} {i : Instr}
    (hf : code.fetch s.pc = some (.base i)) :
    Rv64Verifier.step code s = RiscvZkvm.Rv64.step { s with code := code.baseMap } := by
  unfold Rv64Verifier.step
  rw [hf]

theorem step_word {code : Code} {s : MachineState} {op : WordOp} {rd a b : Reg}
    (hf : code.fetch s.pc = some (.word op rd a b)) :
    Rv64Verifier.step code s = some ((s.setReg rd ((wordResult op ((s.getReg a).truncate 32)
      ((s.getReg b).truncate 32)).signExtend 64)).setPC (s.pc + 4)) := by
  unfold Rv64Verifier.step
  rw [hf]

theorem step_shiftw {code : Code} {s : MachineState} {op : ShiftOp} {rd a : Reg} {sh : BitVec 5}
    (hf : code.fetch s.pc = some (.shiftw op rd a sh)) :
    Rv64Verifier.step code s = some ((s.setReg rd ((shiftResult op ((s.getReg a).truncate 32)
      sh).signExtend 64)).setPC (s.pc + 4)) := by
  unfold Rv64Verifier.step
  rw [hf]

/-- One machine step agrees with the micro-semantics on every classified instruction. -/
theorem classify_sound {code : Code} {s : MachineState} {i : Instruction} {m : Micro}
    (hf : code.fetch s.pc = some i) (h : classify i = some m) :
    Rv64Verifier.step code s = (m.exec s).map fun t => { t with code := codeAfter code s i } := by
  cases i with
  | base i =>
    have hu : ({ s with code := code.baseMap } : MachineState).code s.pc = some i := by
      show code.baseMap s.pc = some i
      unfold Code.baseMap
      rw [hf]
    rw [step_base hf, classify_base_sound hu h]
    exact Micro.exec_withCode s code.baseMap m
  | word op rd a b =>
    simp only [classify, Option.some.injEq] at h; subst h
    rw [step_word hf]
    simp only [Micro.exec, Src.eval, BinOp.eval, Option.map_some, codeAfter]
    exact congrArg some (withCode_eq _ (by simp)).symm
  | shiftw op rd a sh =>
    simp only [classify, Option.some.injEq] at h; subst h
    rw [step_shiftw hf, shiftResult_eq]
    simp only [Micro.exec, Src.eval, BinOp.eval, Option.map_some, codeAfter]
    exact congrArg some (withCode_eq _ (by simp)).symm

end Rv64Verifier.Sym
