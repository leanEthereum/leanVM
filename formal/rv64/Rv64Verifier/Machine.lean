import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode

/-!
# The machine

The RV64IM machine the image runs on: riscv-zkvm's `Rv64.step` for every instruction its `Instr`
models, and the 32-bit word operations it leaves out (`ADDW`..`REMUW`, `SLLIW`, `SRLIW`, `SRAIW`),
defined here as the RISC-V specification defines them; `Rv64Verifier/SailWordOps.lean` proves them
equal to Sail's. Code is a separate, immutable map from addresses to encodings, decoded at fetch. A run
ends when `step` gives `none`: on `HALT` (`ECALL` with `t0 = 0`), the verdict in `a0`, or on a
trap.
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

/-- The register-register 32-bit operations, `OP-32`. -/
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq, Repr

/-- The 32-bit immediate shifts, `OP-IMM-32` but `ADDIW`. -/
inductive ShiftOp where
  | sll | srl | sra
  deriving DecidableEq, Repr

inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | shiftw (op : ShiftOp) (rd rs1 : Reg) (shamt : BitVec 5)
  deriving Repr

/-- One 32-bit encoding: the word operations here, everything else riscv-zkvm's decoder. -/
def decodeInstruction (word : BitVec 32) : Option Instruction :=
  let opcode := (word.extractLsb' 0 7).toNat
  let rd := regOfBits (word.extractLsb' 7 5)
  let rs1 := regOfBits (word.extractLsb' 15 5)
  let rs2 := regOfBits (word.extractLsb' 20 5)
  let f3 := (word.extractLsb' 12 3).toNat
  let f7 := (word.extractLsb' 25 7).toNat
  if opcode = 0x3b then
    let op? : Option WordOp := match f7, f3 with
      | 0, 0 => some .add | 0x20, 0 => some .sub | 0, 1 => some .sll | 0, 5 => some .srl
      | 0x20, 5 => some .sra | 1, 0 => some .mul | 1, 4 => some .div | 1, 5 => some .divu
      | 1, 6 => some .rem | 1, 7 => some .remu | _, _ => none
    op?.map fun op => .word op rd rs1 rs2
  else if opcode = 0x1b ∧ f3 ≠ 0 then
    let op? : Option ShiftOp := match f7, f3 with
      | 0, 1 => some .sll | 0, 5 => some .srl | 0x20, 5 => some .sra | _, _ => none
    op?.map fun op => .shiftw op rd rs1 (word.extractLsb' 20 5)
  else
    (decode word).map .base

/-- An `OP-32` result: shifts take the low five bits of `b`; division by zero gives all ones and
remainder by zero gives `a`, signed overflow gives `a` and zero, as RISC-V specifies. -/
def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b

def shiftResult (op : ShiftOp) (a : BitVec 32) (shamt : BitVec 5) : BitVec 32 :=
  match op with
  | .sll => a <<< shamt.toNat
  | .srl => a >>> shamt.toNat
  | .sra => a.sshiftRight shamt.toNat

/-- Code: instruction encodings at `base`, `base + 4`, ... -/
structure Code where
  base : Word
  words : List (BitVec 32)

def Code.fetch (code : Code) (pc : Word) : Option Instruction :=
  if code.base.toNat ≤ pc.toNat ∧ pc.toNat % 4 = 0 then
    (code.words[(pc.toNat - code.base.toNat) / 4]?).bind decodeInstruction
  else none

/-- riscv-zkvm's code map of the image: its instructions that `Instr` models. -/
def Code.baseMap (code : Code) : CodeMem := fun pc =>
  match code.fetch pc with
  | some (.base instruction) => some instruction
  | _ => none

/-- One step. A base instruction is riscv-zkvm's `step` with the image's code in place; a word
operation writes `rd` sign-extended and moves on. `none` is a halt or a trap. -/
def step (code : Code) (s : MachineState) : Option MachineState :=
  match code.fetch s.pc with
  | none => none
  | some (.base _) => RiscvZkvm.Rv64.step { s with code := code.baseMap }
  | some (.word op rd rs1 rs2) =>
      let value := wordResult op ((s.getReg rs1).truncate 32) ((s.getReg rs2).truncate 32)
      some ((s.setReg rd (value.signExtend 64)).setPC (s.pc + 4))
  | some (.shiftw op rd rs1 shamt) =>
      let value := shiftResult op ((s.getReg rs1).truncate 32) shamt
      some ((s.setReg rd (value.signExtend 64)).setPC (s.pc + 4))

/-- `n` steps from `s` reach `t`. -/
def Steps (code : Code) : Nat → MachineState → MachineState → Prop
  | 0, s, t => s = t
  | n + 1, s, t => ∃ s', step code s = some s' ∧ Steps code n s' t

/-- The `HALT` call: `ECALL` with `t0 = 0`. -/
def Halting (code : Code) (s : MachineState) : Prop :=
  code.fetch s.pc = some (.base .ECALL) ∧ s.getReg .x5 = 0

/-- From `s` the machine halts after `n` steps with `a0 = verdict`. -/
def HaltsWith (code : Code) (s : MachineState) (n : Nat) (verdict : Word) : Prop :=
  ∃ t, Steps code n s t ∧ Halting code t ∧ t.getReg .x10 = verdict

end Rv64Verifier
