module

public import NativeRustcX64.Spec.Keccak
public import NativeVm.Model.Field
public import Statement.LeanVmVerifier
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.Kinv.Names
public import NativeRustcVmX64.Code.Vm.KinvSq.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names

/-!
# The contracts of `field.rs`'s functions on x86-64

Each function uses the stack below RSP (`<fn>Stack` bytes: its pushes, its frame, its callees'
return addresses and stacks; `StackOk` in its precondition, which also maps its return address at
RSP) and returns with the callee-saved registers kept (and RSP 8 above, `Spec`), no byte changed
outside that stack (`stackBelow`). Its result is the model's (`NativeVm.Model`), a register's
value read as the model's word (`UInt64.ofBitVec`):

- `kmul(a, b)` (RDI, RSI): `Model.kmul a b` in RAX.
- `EW::mul(x, y)` (`x` in RDI, RSI, `y` in RDX, RCX): `Model.EW.mul x y` in RAX, RDX.
- `kinv::sq(v, n)` (RDI, ESI, `n ≠ 0`): `v` squared `n` times (`kmul v v`) in RAX.
- `kinv(a)` (RDI): `Model.kinv a` in RAX.
- `kpow(n)` (RDI; rustc specialised `kpow(a, n)` to its only base, `2`): `Model.gpowK n` in RAX.
- `EW::sq_iter(k, x)` (RDI, `x` in RSI, RDX): `Model.EW.sqIter k x` in RAX, RDX.
- `bit_length(v)` (RDI): the bit length of `v` (`Verifier.bitLength`, `0` at `0`) in RAX.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model

@[expose] public section

/-! ## Stacks -/

/-- The stack `kmul` uses: its 6 pushes. -/
def kmulStack : Nat := 48
/-- The stack `EW::mul` uses: its 6 pushes and its 96-byte frame. -/
def ewMulStack : Nat := 144
/-- The stack `kinv::sq` uses: its push, `kmul`'s return address and stack. -/
def kinvSqStack : Nat := 16 + kmulStack
/-- The stack `kinv` uses: its 3 pushes, its callees' return address and stacks (`kinv::sq`'s,
`kmul`'s included). -/
def kinvStack : Nat := 32 + kinvSqStack
/-- The stack `kpow` uses: its 3 pushes, `kmul`'s return address and stack. -/
def kpowStack : Nat := 32 + kmulStack
/-- The stack `EW::sq_iter` uses: its push, `EW::mul`'s return address and stack. -/
def ewSqIterStack : Nat := 16 + ewMulStack
/-- `bit_length` uses no stack. -/
def bitLengthStack : Nat := 0

/-! ## Values -/

/-- `v` squared `n` times in `K`. -/
def ksqIter (n : Nat) (v : UInt64) : UInt64 := Nat.repeat (fun v ↦ kmul v v) n v

/-- `kinv::sq`'s count: ESI. -/
def kinvSqCount (m : MachineData) : Nat := (reg m .rsi).toNat % 2 ^ 32

/-! ## Contracts -/

/-- `kmul`'s precondition. -/
def KmulPre (m : MachineData) : Prop := StackOk m kmulStack

/-- `kmul`'s postcondition. -/
def KmulPost (m m' : MachineData) : Prop :=
  reg m' .rax = (kmul (.ofBitVec (reg m .rdi)) (.ofBitVec (reg m .rsi))).toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kmulStack) kmulStack) ∧ Saved m m'

/-- `EW::mul`'s precondition. -/
def EWMulPre (m : MachineData) : Prop := StackOk m ewMulStack

/-- `EW::mul`'s postcondition. -/
def EWMulPost (m m' : MachineData) : Prop :=
  reg m' .rax = (EW.mul ⟨.ofBitVec (reg m .rdi), .ofBitVec (reg m .rsi)⟩
      ⟨.ofBitVec (reg m .rdx), .ofBitVec (reg m .rcx)⟩).c0.toBitVec ∧
    reg m' .rdx = (EW.mul ⟨.ofBitVec (reg m .rdi), .ofBitVec (reg m .rsi)⟩
      ⟨.ofBitVec (reg m .rdx), .ofBitVec (reg m .rcx)⟩).c1.toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m ewMulStack) ewMulStack) ∧ Saved m m'

/-- `kinv::sq`'s precondition: a nonzero count. -/
def KinvSqPre (m : MachineData) : Prop := StackOk m kinvSqStack ∧ kinvSqCount m ≠ 0

/-- `kinv::sq`'s postcondition. -/
def KinvSqPost (m m' : MachineData) : Prop :=
  reg m' .rax = (ksqIter (kinvSqCount m) (.ofBitVec (reg m .rdi))).toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kinvSqStack) kinvSqStack) ∧ Saved m m'

/-- `kinv`'s precondition. -/
def KinvPre (m : MachineData) : Prop := StackOk m kinvStack

/-- `kinv`'s postcondition. -/
def KinvPost (m m' : MachineData) : Prop :=
  reg m' .rax = (kinv (.ofBitVec (reg m .rdi))).toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kinvStack) kinvStack) ∧ Saved m m'

/-- `kpow`'s precondition. -/
def KpowPre (m : MachineData) : Prop := StackOk m kpowStack

/-- `kpow`'s postcondition: `2 ^ n`. -/
def KpowPost (m m' : MachineData) : Prop :=
  reg m' .rax = (gpowK (reg m .rdi).toNat).toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kpowStack) kpowStack) ∧ Saved m m'

/-- `EW::sq_iter`'s precondition. -/
def EWSqIterPre (m : MachineData) : Prop := StackOk m ewSqIterStack

/-- `EW::sq_iter`'s postcondition. -/
def EWSqIterPost (m m' : MachineData) : Prop :=
  reg m' .rax =
      (EW.sqIter (reg m .rdi).toNat ⟨.ofBitVec (reg m .rsi), .ofBitVec (reg m .rdx)⟩).c0.toBitVec ∧
    reg m' .rdx =
      (EW.sqIter (reg m .rdi).toNat ⟨.ofBitVec (reg m .rsi), .ofBitVec (reg m .rdx)⟩).c1.toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m ewSqIterStack) ewSqIterStack) ∧
    Saved m m'

/-- `bit_length`'s precondition: its return address mapped. -/
def BitLengthPre (m : MachineData) : Prop := StackOk m bitLengthStack

/-- `bit_length`'s postcondition. -/
def BitLengthPost (m m' : MachineData) : Prop :=
  (reg m' .rax).toNat = LeanVM.Protocol.Verifier.bitLength (reg m .rdi).toNat ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m bitLengthStack) bitLengthStack) ∧ Saved m m'

end

end NativeRustcVmX64
