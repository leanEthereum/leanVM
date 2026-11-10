import Rv64Verifier.Proofs.Layout.ContractsVec

/-!
# Contracts of the functions that push a pair of flushes

As `ContractsVec.lean`: each grows a `Flushes` in place (`GrowFlushes`), cloning the forms it is
given, so the `Flushes` reaches only fresh buffers beyond what it reached.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-! ## `Flushes::counted`, at `0x8000525c` -/

@[rv_addr] def countedStack : Nat := 192 + colStack

/-- `a0` = `self`; `a1` = the prefix, two forms; `a2` = the counter, a form; `a3` = `count`; `a4`,
`a5` = the suffix, a slice of forms. The call clones all three, and writes none of them. -/
structure CountedPre (s : MachineState) : Prop extends FlushesPre countedStack s where
  pre : ValidMemRange (s.getReg .x11) 6
  preOk : FormsOk s (s.getReg .x11) 2
  preFree : Outside s (s.getReg .x11) 48
  preStack : Apart (s.getReg .x11) 48 (stackLo s countedStack) countedStack
  counter : ValidMemRange (s.getReg .x12) 3
  counterOk : FormOk s (s.getReg .x12)
  counterFree : Outside s (s.getReg .x12) 24
  counterStack : Apart (s.getReg .x12) 24 (stackLo s countedStack) countedStack
  suf : ValidMemRange (s.getReg .x14) (3 * (s.getReg .x15).toNat)
  sufOk : FormsOk s (s.getReg .x14) (s.getReg .x15).toNat
  sufFree : Outside s (s.getReg .x14) (24 * (s.getReg .x15).toNat)
  sufStack : Apart (s.getReg .x14) (24 * (s.getReg .x15).toNat) (stackLo s countedStack)
    countedStack

def CountedSpec : Prop := FunSpec Image.code 0x8000525c CountedPre fun s t ↦
  GrowFlushes s t (s.getReg .x10) countedStack (fun _ ↦ False) ∧
    flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).counted
      (formsAt s (s.getReg .x11) 2) (formOf s (s.getReg .x12)) (s.getReg .x13).toNat
      (formsAt s (s.getReg .x14) (s.getReg .x15).toNat)

/-! ## `Flushes::memory`, at `0x800051b0` -/

@[rv_addr] def memoryStack : Nat := 112 + countedStack

/-- `a0` = `self`; `a1` = the address, a form (moved); `a2` = `count`; `a3` = the values, three
forms. -/
structure MemoryPre (s : MachineState) : Prop extends FlushesPre memoryStack s where
  address : ValidMemRange (s.getReg .x11) 3
  addressOk : FormOk s (s.getReg .x11)
  addressFree : Outside s (s.getReg .x11) 24
  addressStack : Apart (s.getReg .x11) 24 (stackLo s memoryStack) memoryStack
  values : ValidMemRange (s.getReg .x13) 9
  valuesOk : FormsOk s (s.getReg .x13) 3
  valuesFree : Outside s (s.getReg .x13) 72
  valuesStack : Apart (s.getReg .x13) 72 (stackLo s memoryStack) memoryStack

def MemorySpec : Prop := FunSpec Image.code 0x800051b0 MemoryPre fun s t ↦
  GrowFlushes s t (s.getReg .x10) memoryStack (fun _ ↦ False) ∧
    flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).memory
      (formOf s (s.getReg .x11)) (s.getReg .x12).toNat (formsAt s (s.getReg .x13) 3)

end Rv64Verifier.Layout
