module

public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Code.Vm.Seed.Names
public import NativeRustcVmArm.Code.Vm.Verify.Names
public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Rodata
public import NativeRustcVm.Top.Entry

/-!
# The contracts of `verify.rs`'s `seed`, `verify_execution`, `verify` and of `leanvm_verify` on
AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. `seed` reads the round constants (`RcAt`), the others the
read-only data (`RodataAt`), apart from the areas they are given (`RodataApart`).

- `seed(out, bc, n, pub)` (X0 to X3; `out` the 200-byte `sret` state): the 25 words at `out`
  become `Model.seed` of the `n` bytecode words at `bc` and the four public words at `pub`.
- `verify_execution(t, bc, n, pub, w)` (X0 to X4): the `TState` at `t` representing `s`, the
  working area at `w` (`workAreaBytes`): X0 is `okWord` of the walk's success
  (`Model.verifyExecution`), and on `some` the `TState` represents the walk's last state.
- `verify(bc, n, pub, dec, w)` (X0 to X4; `dec` points to the 24-byte `Decoded` naming the decoded
  area `a`, which holds `stream` and `openings`): X0 is `1` when `Model.verify` accepts, else `0`.
- `leanvm_verify(ctx)` (X0): from `NativeVm.Entry.EntryPre` on the word view of memory, the
  alignment it checks (`NativeRustcVm.Top.Aligned`), the caller's areas apart from its stack and
  the read-only data: X0 is `1` exactly when the wire bytes decode (`Proof.fromBytes`) to a proof
  `verifyWith` accepts, else `0`.

The bytecode slice is a dangling pointer when empty (`8`): its apartness is asked only when
`n > 0`.
-/

namespace NativeRustcVmArm

open NativeRustcVm NativeRustcVm.Transcript NativeRustcVm.Top NativeVm NativeVm.Model
open NativeRustcArm (Spec StackOk Saved stackBelow)
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- The stack `seed` uses: its 240-byte frame and `keccak256_words`'s (`keccak_f` uses less,
`memset` and `memcpy` none). -/
def seedStack : Nat := 240 + keccak256WordsStack
/-- The stack `verify_execution` uses: its 96-byte frame and `verify_bus_balance`'s, the deepest of
its callees' (18288 bytes). -/
def verifyExecutionStack : Nat := 96 + 18288
/-- The stack `verify` uses: its 832-byte frame (the `TState` at SP + 8) and
`verify_execution`'s. -/
def verifyStack : Nat := 832 + verifyExecutionStack
/-- The stack `leanvm_verify` uses: its 128-byte frame (the public input at SP + 8, the `Decoded`
at SP + 40) and `verify`'s. -/
def leanvmVerifyStack : Nat := 128 + verifyStack

section
variable [Labels]

/-! ## `seed` -/

/-- `seed`'s precondition. -/
def SeedPre (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let bc := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let pub := m.regs.X3.toBitVec
  StackOk m seedStack ∧ RcAt m seedStack ∧ 9 + 8 * n < 2 ^ 32 ∧
    Region.Ok m.dmem ⟨bc, 8 * n⟩ ∧ Region.Ok m.dmem ⟨pub, 32⟩ ∧ Region.Ok m.dmem ⟨out, 200⟩ ∧
    Disjoint [stackR m seedStack, ⟨pub, 32⟩] ∧ Disjoint [stackR m seedStack, ⟨out, 200⟩] ∧
    (0 < n → Apart bc (8 * n) (stackBelow m seedStack) seedStack)

/-- `seed`'s postcondition. -/
def SeedPost (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let bc := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let pub := m.regs.X3.toBitVec
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem bc w →
    ∀ P : Vector UInt64 4, NativeRustcVm.WordsAt m.dmem pub P.toList →
      NativeRustcVm.WordsAt m'.dmem out (seed w.toArray P).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 200 p ∨
      InRange (stackBelow m seedStack) seedStack p) ∧ Saved m m'

/-- The regions apart from the read-only data. -/
def ApartRodata (rs : List Region) : Prop := ∀ r ∈ rs, RodataApart r.addr r.size

/-! ## `verify_execution` -/

/-- `verify_execution`'s precondition: the `TState` at `t` represents `s` with the decoded area
`a`, no root read yet. -/
def VerifyExecutionPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let bc := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let pub := m.regs.X3.toBitVec; let w := m.regs.X4.toBitVec
  StackOk m verifyExecutionStack ∧ RodataAt m verifyExecutionStack ∧ 9 + 8 * n < 2 ^ 32 ∧
    TStateAt m.dmem t a s ∧ s.roots.size = 0 ∧ Region.Ok m.dmem ⟨bc, 8 * n⟩ ∧
    Region.Ok m.dmem ⟨pub, 32⟩ ∧
    Region.Ok m.dmem ⟨w, workAreaBytes⟩ ∧
    Disjoint [stackR m verifyExecutionStack, ⟨t, tstateBytes⟩, a.region, ⟨pub, 32⟩,
      ⟨w, workAreaBytes⟩] ∧
    ApartRodata [⟨t, tstateBytes⟩, a.region, ⟨pub, 32⟩, ⟨w, workAreaBytes⟩] ∧
    (0 < n → Disjoint [stackR m verifyExecutionStack, ⟨bc, 8 * n⟩, ⟨t, tstateBytes⟩, a.region,
      ⟨w, workAreaBytes⟩] ∧ RodataApart bc (8 * n))

/-- `verify_execution`'s postcondition. -/
def VerifyExecutionPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let bc := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let pub := m.regs.X3.toBitVec; let w := m.regs.X4.toBitVec
  (∀ bcw : List UInt64, bcw.length = n → NativeRustcVm.WordsAt m.dmem bc bcw →
    ∀ P : Vector UInt64 4, NativeRustcVm.WordsAt m.dmem pub P.toList →
      let r := (verifyExecution bcw.toArray P).run s
      m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨t, tstateBytes⟩, ⟨w, workAreaBytes⟩,
      stackR m verifyExecutionStack]) ∧ Saved m m'

/-! ## `verify` -/

/-- `verify`'s precondition: the `Decoded` at `dec` names the area `a`, which holds `stream` and
`openings`. -/
def VerifyPre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let bc := m.regs.X0.toBitVec; let n := m.regs.X1.toNat; let pub := m.regs.X2.toBitVec
  let dec := m.regs.X3.toBitVec; let w := m.regs.X4.toBitVec
  StackOk m verifyStack ∧ RodataAt m verifyStack ∧ 9 + 8 * n < 2 ^ 32 ∧
    DecFieldsAt m.dmem dec a ∧ DecodedAt m.dmem a stream openings ∧
    Region.Ok m.dmem ⟨bc, 8 * n⟩ ∧ Region.Ok m.dmem ⟨pub, 32⟩ ∧ Region.Ok m.dmem ⟨dec, 24⟩ ∧
    Region.Ok m.dmem a.region ∧ Region.Ok m.dmem ⟨w, workAreaBytes⟩ ∧
    Disjoint [stackR m verifyStack, ⟨pub, 32⟩, ⟨dec, 24⟩, a.region, ⟨w, workAreaBytes⟩] ∧
    ApartRodata [⟨pub, 32⟩, ⟨dec, 24⟩, a.region, ⟨w, workAreaBytes⟩] ∧
    (0 < n → Disjoint [stackR m verifyStack, ⟨bc, 8 * n⟩, a.region, ⟨w, workAreaBytes⟩] ∧
      RodataApart bc (8 * n))

/-- `verify`'s postcondition. -/
def VerifyPost (stream : Array EW) (openings : Array (Array OpeningW)) (m m' : MachineData) :
    Prop :=
  let bc := m.regs.X0.toBitVec; let n := m.regs.X1.toNat; let pub := m.regs.X2.toBitVec
  let w := m.regs.X4.toBitVec
  (∀ bcw : List UInt64, bcw.length = n → NativeRustcVm.WordsAt m.dmem bc bcw →
    ∀ P : Vector UInt64 4, NativeRustcVm.WordsAt m.dmem pub P.toList →
      m'.regs.X0 = if Model.verify bcw.toArray P stream openings then 1 else 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨w, workAreaBytes⟩, stackR m verifyStack]) ∧ Saved m m'

/-! ## `leanvm_verify` -/

/-- `leanvm_verify`'s precondition: the context at X0 as `EntryPre` describes it, the alignment
it checks, the caller's areas (those not empty) apart from its stack and the read-only data. -/
def LeanvmVerifyPre (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m : MachineData) : Prop :=
  let ctx := m.regs.X0
  StackOk m leanvmVerifyStack ∧ RodataAt m leanvmVerifyStack ∧
    NativeVm.Entry.EntryPre (NativeRustcVm.wordView m.dmem) ctx a bytes bytecode pub ∧
    Aligned a bytes.length bytecode.length ∧
    ApartFrom (entryRegions ctx a bytes.length bytecode.length) (stackBelow m leanvmVerifyStack)
      leanvmVerifyStack ∧
    ∀ r ∈ entryRegions ctx a bytes.length bytecode.length, 0 < r.size → RodataApart r.addr r.size

/-- The verdict: `1` when the wire bytes decode (`Proof.fromBytes`) to a proof `verifyWith`
accepts, else `0`. -/
def verdictWord (bytes : List UInt8) (bytecode : List UInt64) (pub : Vector UInt64 4) : UInt64 :=
  if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
      (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
    then 1 else 0

/-- `leanvm_verify`'s postcondition. -/
def LeanvmVerifyPost (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m m' : MachineData) : Prop :=
  m'.regs.X0 = verdictWord bytes bytecode pub ∧
    SameOutside m.dmem m'.dmem (InAny [⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩,
      ⟨a.work.toBitVec, workAreaBytes⟩, stackR m leanvmVerifyStack]) ∧ Saved m m'

end

end

end NativeRustcVmArm
