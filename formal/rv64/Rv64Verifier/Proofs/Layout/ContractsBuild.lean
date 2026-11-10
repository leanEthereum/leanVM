import Rv64Verifier.Proofs.Layout.ContractsFlushes

/-!
# Contracts of the functions that build a table's flushes

As `ContractsFlushes.lean`.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- The `n` `usize`s from `p`. -/
def colsAt (s : MachineState) (p : Word) (n : Nat) : List Nat :=
  (List.range n).map fun i ↦ (s.getMem (p + BitVec.ofNat 64 (8 * i))).toNat

/-! ## `Flushes::memory_cols`, at `0x80005c64` -/

@[rv_addr] def memoryColsStack : Nat := 240 + memoryStack

/-- `a0` = `self`; `a1` = the address, a form (moved); `a2` = `count`; `a3`, `a4` = the columns, a
slice of one to three `usize`s (the code reads the first unconditionally, and takes four or more
as two). -/
structure MemoryColsPre (s : MachineState) : Prop extends FlushesPre memoryColsStack s where
  address : ValidMemRange (s.getReg .x11) 3
  addressOk : FormOk s (s.getReg .x11)
  addressFree : Outside s (s.getReg .x11) 24
  addressStack : Apart (s.getReg .x11) 24 (stackLo s memoryColsStack) memoryColsStack
  len : 1 ≤ (s.getReg .x14).toNat ∧ (s.getReg .x14).toNat ≤ 3
  columns : ValidMemRange (s.getReg .x13) (s.getReg .x14).toNat
  columnsFree : Outside s (s.getReg .x13) (8 * (s.getReg .x14).toNat)
  columnsStack : Apart (s.getReg .x13) (8 * (s.getReg .x14).toNat) (stackLo s memoryColsStack)
    memoryColsStack

def MemoryColsSpec : Prop := FunSpec Image.code 0x80005c64 MemoryColsPre fun s t ↦
  GrowFlushes s t (s.getReg .x10) memoryColsStack (fun _ ↦ False) ∧
    flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).memoryCols
      (formOf s (s.getReg .x11)) (s.getReg .x12).toNat
      (colsAt s (s.getReg .x13) (s.getReg .x14).toNat)

/-! ## `Flushes::bytecode`, at `0x80004b94`, compiled for `pc = 0` -/

@[rv_addr] def bytecodeStack : Nat := 144 + countedStack

/-- `a0` = `self`; `a1` = `count`; `a2` = `opcode`; `a3` = the operands, a `Vec<Form>` (moved). -/
structure BytecodePre (s : MachineState) : Prop extends FlushesPre bytecodeStack s where
  ops : ValidMemRange (s.getReg .x13) 3
  opsOk : FormVecOk s (s.getReg .x13)
  opsFree : Outside s (s.getReg .x13) 24
  opsStack : Apart (s.getReg .x13) 24 (stackLo s bytecodeStack) bytecodeStack
  opsBuf : Outside s (vecPtr s (s.getReg .x13)) (24 * (vecLen s (s.getReg .x13)).toNat)
  opsBufStack : Apart (vecPtr s (s.getReg .x13)) (24 * (vecLen s (s.getReg .x13)).toNat)
    (stackLo s bytecodeStack) bytecodeStack

def BytecodeSpec : Prop := FunSpec Image.code 0x80004b94 BytecodePre fun s t ↦
  GrowFlushes s t (s.getReg .x10) bytecodeStack (fun _ ↦ False) ∧
    flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).bytecode 0 (s.getReg .x11).toNat
      (s.getReg .x12).toNat (formVecOf s (s.getReg .x13))

end Rv64Verifier.Layout
