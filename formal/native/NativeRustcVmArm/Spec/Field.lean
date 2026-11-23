module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.Kinv.Names
public import NativeRustcVmArm.Code.Vm.KinvSq.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcArm.Spec.Keccak
public import NativeVm.Model.Field
public import Statement.LeanVmVerifier

/-!
# The contracts of `field.rs`'s functions on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept, no byte changed outside that
stack (`stackBelow`). Its result is the model's (`NativeVm.Model`):

- `kmul(a, b)` (X0, X1): `Model.kmul a b` in X0.
- `EW::mul(x, y)` (`x` in X0, X1, `y` in X2, X3): `Model.EW.mul x y` in X0, X1.
- `kinv::sq(v, n)` (X0, W1, `n ≠ 0`): `v` squared `n` times (`kmul v v`) in X0.
- `kinv(a)` (X0): `Model.kinv a` in X0.
- `kpow(n)` (X0; rustc specialised `kpow(a, n)` to its only base, `2`): `Model.gpowK n` in X0.
- `EW::sq_iter(k, x)` (X0, `x` in X1, X2): `Model.EW.sqIter k x` in X0, X1.
- `bit_length(v)` (X0): the bit length of `v` (`Verifier.bitLength`, `0` at `0`) in X0.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- The stack `kmul` uses: its 112-byte frame. -/
def kmulStack : Nat := 112
/-- The stack `EW::mul` uses: its 96-byte frame and 496 bytes of spills. -/
def ewMulStack : Nat := 592
/-- The stack `kinv::sq` uses, `kmul`'s included. -/
def kinvSqStack : Nat := 16 + kmulStack
/-- The stack `kinv` uses, `kinv::sq`'s included. -/
def kinvStack : Nat := 32 + kinvSqStack
/-- The stack `kpow` uses, `kmul`'s included. -/
def kpowStack : Nat := 32 + kmulStack
/-- The stack `EW::sq_iter` uses, `EW::mul`'s included. -/
def ewSqIterStack : Nat := 16 + ewMulStack
/-- `bit_length` uses no stack. -/
def bitLengthStack : Nat := 0

/-! ## Values -/

/-- `v` squared `n` times in `K`. -/
def ksqIter (n : Nat) (v : UInt64) : UInt64 := Nat.repeat (fun v ↦ kmul v v) n v

/-- `kinv::sq`'s count: W1. -/
def kinvSqCount (m : MachineData) : Nat := m.regs.X1.toNat % 2 ^ 32

/-! ## Contracts -/

/-- `kmul`'s precondition. -/
def KmulPre (m : MachineData) : Prop := StackOk m kmulStack

/-- `kmul`'s postcondition. -/
def KmulPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = kmul m.regs.X0 m.regs.X1 ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kmulStack) kmulStack) ∧ Saved m m'

/-- `EW::mul`'s precondition. -/
def EWMulPre (m : MachineData) : Prop := StackOk m ewMulStack

/-- `EW::mul`'s postcondition. -/
def EWMulPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = (EW.mul ⟨m.regs.X0, m.regs.X1⟩ ⟨m.regs.X2, m.regs.X3⟩).c0 ∧
    m'.regs.X1 = (EW.mul ⟨m.regs.X0, m.regs.X1⟩ ⟨m.regs.X2, m.regs.X3⟩).c1 ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m ewMulStack) ewMulStack) ∧ Saved m m'

/-- `kinv::sq`'s precondition: a nonzero count. -/
def KinvSqPre (m : MachineData) : Prop := StackOk m kinvSqStack ∧ kinvSqCount m ≠ 0

/-- `kinv::sq`'s postcondition. -/
def KinvSqPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = ksqIter (kinvSqCount m) m.regs.X0 ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kinvSqStack) kinvSqStack) ∧ Saved m m'

/-- `kinv`'s precondition. -/
def KinvPre (m : MachineData) : Prop := StackOk m kinvStack

/-- `kinv`'s postcondition. -/
def KinvPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = kinv m.regs.X0 ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kinvStack) kinvStack) ∧ Saved m m'

/-- `kpow`'s precondition. -/
def KpowPre (m : MachineData) : Prop := StackOk m kpowStack

/-- `kpow`'s postcondition: `2 ^ n`. -/
def KpowPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = gpowK m.regs.X0.toNat ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kpowStack) kpowStack) ∧ Saved m m'

/-- `EW::sq_iter`'s precondition. -/
def EWSqIterPre (m : MachineData) : Prop := StackOk m ewSqIterStack

/-- `EW::sq_iter`'s postcondition. -/
def EWSqIterPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = (EW.sqIter m.regs.X0.toNat ⟨m.regs.X1, m.regs.X2⟩).c0 ∧
    m'.regs.X1 = (EW.sqIter m.regs.X0.toNat ⟨m.regs.X1, m.regs.X2⟩).c1 ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m ewSqIterStack) ewSqIterStack) ∧
    Saved m m'

/-- `bit_length`'s precondition. -/
def BitLengthPre (_ : MachineData) : Prop := True

/-- `bit_length`'s postcondition. -/
def BitLengthPost (m m' : MachineData) : Prop :=
  m'.regs.X0.toNat = LeanVM.Protocol.Verifier.bitLength m.regs.X0.toNat ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m bitLengthStack) bitLengthStack) ∧ Saved m m'

end

end NativeRustcVmArm
