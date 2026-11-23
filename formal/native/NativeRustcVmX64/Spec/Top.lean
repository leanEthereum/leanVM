module

public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVmX64.Spec.Transcript
public import NativeRustcVmX64.Rodata
public import NativeRustcVmX64.Got
public import NativeRustcVm.Top.Entry
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmX64.Code.Vm.Seed.Names
public import NativeRustcVmX64.Code.Vm.Verify.Names
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names

/-!
# The contracts of `verify.rs`'s `seed`, `verify_execution`, `verify` and of `leanvm_verify` on
x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Top`) with the System V registers: arguments in RDI,
RSI, RDX, RCX, R8. Each function uses the stack below RSP (`<fn>Stack` bytes: its pushes, its
frame, its callees' return addresses and stacks; `StackOk` in its precondition also maps the return
address at RSP, so the areas it is given are apart from `stackR`, the stack with the return
address) and returns with the callee-saved registers kept (and RSP 8 above, `Spec`), no byte
changed outside its outputs and its frame (`frameR`, the stack without the return address). `seed`
reads the round constants (`RcAt`), the others the read-only data (`RodataAt`), apart from the
areas they are given (`RodataApart`).

- `seed(out, bc, n, pub)` (RDI to RCX; `out` the 200-byte `sret` state): the 25 words at `out`
  become `Model.seed` of the `n` bytecode words at `bc` and the four public words at `pub`.
- `verify_execution(t, bc, n, pub, w)` (RDI to R8): the `TState` at `t` representing `s`, the
  working area at `w` (`workAreaBytes`): AL is `okWord` of the walk's success
  (`Model.verifyExecution`; a `bool`, rustc sets AL alone, `OkAl`), and on `some` the `TState`
  represents the walk's last state.
- `verify(bc, n, pub, dec, w)` (RDI to R8; `dec` points to the 24-byte `Decoded` naming the decoded
  area `a`, which holds `stream` and `openings`): AL is `1` when `Model.verify` accepts, else `0`
  (a `bool`, `OkAl`).
- `leanvm_verify(ctx)` (RDI): from `NativeVm.Entry.EntryPre` on the word view of memory, the
  alignment it checks (`NativeRustcVm.Top.Aligned`), the caller's areas apart from its stack and
  the read-only data: RAX is `1` exactly when the wire bytes decode (`Proof.fromBytes`) to a proof
  `verifyWith` accepts, else `0` (all of RAX: `movzbl %al, %eax` or `xorl %eax, %eax`).

The bytecode slice is a dangling pointer when empty (`8`): its apartness is asked only when
`n > 0`.
-/

namespace NativeRustcVmX64

open NativeRustcVm NativeRustcVm.Transcript NativeRustcVm.Top NativeVm NativeVm.Model
open NativeRustcX64 (Spec StackOk Saved stackBelow rspOf reg)
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Stacks -/

/-- The stack `seed` uses: its 3 pushes, its 208-byte frame (the state at RSP + 8), then
`keccak256_words`'s return address and stack (`keccak_f`'s is smaller, `memset` and `memcpy` use
only their return addresses). -/
def seedStack : Nat := 24 + 208 + 8 + keccak256WordsStack
/-- The stack `verify_execution` uses: its 7 pushes (the last, `pushq %rax`, a slot), then
`verify_bus_balance`'s return address and stack, the deepest of its callees' (17824 bytes;
`verify_stacked_opening`, called 32 bytes lower with three argument words, uses 11888). -/
def verifyExecutionStack : Nat := 56 + 8 + 17824
/-- The stack `verify` uses: its 6 pushes, its 760-byte frame (the `TState` at RSP), then
`verify_execution`'s return address and stack. -/
def verifyStack : Nat := 48 + 760 + 8 + verifyExecutionStack
/-- The stack `leanvm_verify` uses: its 6 pushes, its 56-byte frame (the public input at RSP, the
`Decoded` at RSP + 32), then `verify`'s return address and stack (`decode`'s is smaller). -/
def leanvmVerifyStack : Nat := 48 + 56 + 8 + verifyStack

section
variable [Labels]

/-! ## `seed` -/

/-- `seed`'s precondition. -/
def SeedPre (m : MachineData) : Prop :=
  let out := reg m .rdi; let bc := reg m .rsi; let n := (reg m .rdx).toNat
  let pub := reg m .rcx
  StackOk m seedStack ∧ RcAt m seedStack ∧ 9 + 8 * n < 2 ^ 32 ∧
    Region.Ok m.dmem ⟨bc, 8 * n⟩ ∧ Region.Ok m.dmem ⟨pub, 32⟩ ∧ Region.Ok m.dmem ⟨out, 200⟩ ∧
    Disjoint [stackR m seedStack, ⟨pub, 32⟩] ∧ Disjoint [stackR m seedStack, ⟨out, 200⟩] ∧
    (0 < n → Apart bc (8 * n) (stackBelow m seedStack) (seedStack + 8)) ∧
    NativeRustcX64.GotAt m seedStack
      ([(out, 200), (pub, 32), (rcAddr, 192)] ++ if n = 0 then [] else [(bc, 8 * n)])
      ["memcpy", "memset"]

/-- `seed`'s postcondition. -/
def SeedPost (m m' : MachineData) : Prop :=
  let out := reg m .rdi; let bc := reg m .rsi; let n := (reg m .rdx).toNat
  let pub := reg m .rcx
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
  let t := reg m .rdi; let bc := reg m .rsi; let n := (reg m .rdx).toNat
  let pub := reg m .rcx; let w := reg m .r8
  StackOk m verifyExecutionStack ∧ RodataAt m verifyExecutionStack ∧ 9 + 8 * n < 2 ^ 32 ∧
    TStateAt m.dmem t a s ∧ s.roots.size = 0 ∧ Region.Ok m.dmem ⟨bc, 8 * n⟩ ∧
    Region.Ok m.dmem ⟨pub, 32⟩ ∧
    Region.Ok m.dmem ⟨w, workAreaBytes⟩ ∧
    Disjoint [stackR m verifyExecutionStack, ⟨t, tstateBytes⟩, a.region, ⟨pub, 32⟩,
      ⟨w, workAreaBytes⟩] ∧
    ApartRodata [⟨t, tstateBytes⟩, a.region, ⟨pub, 32⟩, ⟨w, workAreaBytes⟩] ∧
    (0 < n → Disjoint [stackR m verifyExecutionStack, ⟨bc, 8 * n⟩, ⟨t, tstateBytes⟩, a.region,
      ⟨w, workAreaBytes⟩] ∧ RodataApart bc (8 * n)) ∧
    NativeRustcX64.GotAt m verifyExecutionStack
      ([(t, tstateBytes), (a.words, 8 * a.len), (pub, 32), (w, workAreaBytes)] ++
        rodataAreas ++ if n = 0 then [] else [(bc, 8 * n)]) ["memcpy", "memset"]

/-- `verify_execution`'s postcondition. -/
def VerifyExecutionPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let bc := reg m .rsi; let n := (reg m .rdx).toNat
  let pub := reg m .rcx; let w := reg m .r8
  (∀ bcw : List UInt64, bcw.length = n → NativeRustcVm.WordsAt m.dmem bc bcw →
    ∀ P : Vector UInt64 4, NativeRustcVm.WordsAt m.dmem pub P.toList →
      let r := (verifyExecution bcw.toArray P).run s
      OkAl m' r.isSome ∧ NextAt m'.dmem t a r) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨t, tstateBytes⟩, ⟨w, workAreaBytes⟩,
      frameR m verifyExecutionStack]) ∧ Saved m m'

/-! ## `verify` -/

/-- `verify`'s precondition: the `Decoded` at `dec` names the area `a`, which holds `stream` and
`openings`. -/
def VerifyPre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let bc := reg m .rdi; let n := (reg m .rsi).toNat; let pub := reg m .rdx
  let dec := reg m .rcx; let w := reg m .r8
  StackOk m verifyStack ∧ RodataAt m verifyStack ∧ 9 + 8 * n < 2 ^ 32 ∧
    DecFieldsAt m.dmem dec a ∧ DecodedAt m.dmem a stream openings ∧
    Region.Ok m.dmem ⟨bc, 8 * n⟩ ∧ Region.Ok m.dmem ⟨pub, 32⟩ ∧ Region.Ok m.dmem ⟨dec, 24⟩ ∧
    Region.Ok m.dmem a.region ∧ Region.Ok m.dmem ⟨w, workAreaBytes⟩ ∧
    Disjoint [stackR m verifyStack, ⟨pub, 32⟩, ⟨dec, 24⟩, a.region, ⟨w, workAreaBytes⟩] ∧
    ApartRodata [⟨pub, 32⟩, ⟨dec, 24⟩, a.region, ⟨w, workAreaBytes⟩] ∧
    (0 < n → Disjoint [stackR m verifyStack, ⟨bc, 8 * n⟩, a.region, ⟨w, workAreaBytes⟩] ∧
      RodataApart bc (8 * n)) ∧
    NativeRustcX64.GotAt m verifyStack
      ([(pub, 32), (dec, 24), (a.words, 8 * a.len), (w, workAreaBytes)] ++
        rodataAreas ++ if n = 0 then [] else [(bc, 8 * n)]) ["memcpy", "memset"]

/-- `verify`'s postcondition. -/
def VerifyPost (stream : Array EW) (openings : Array (Array OpeningW)) (m m' : MachineData) :
    Prop :=
  let bc := reg m .rdi; let n := (reg m .rsi).toNat; let pub := reg m .rdx
  let w := reg m .r8
  (∀ bcw : List UInt64, bcw.length = n → NativeRustcVm.WordsAt m.dmem bc bcw →
    ∀ P : Vector UInt64 4, NativeRustcVm.WordsAt m.dmem pub P.toList →
      OkAl m' (Model.verify bcw.toArray P stream openings)) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨w, workAreaBytes⟩, frameR m verifyStack]) ∧ Saved m m'

/-! ## `leanvm_verify` -/

/-- The context `leanvm_verify` is given: RDI. -/
def ctxOf (m : MachineData) : UInt64 := UInt64.ofBitVec (reg m .rdi)

/-- `leanvm_verify`'s precondition: the context at RDI as `EntryPre` describes it, the alignment
it checks, the caller's areas (those not empty) apart from its stack (with the return address) and
the read-only data. -/
def LeanvmVerifyPre (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m : MachineData) : Prop :=
  let ctx := ctxOf m
  StackOk m leanvmVerifyStack ∧ RodataAt m leanvmVerifyStack ∧
    NativeVm.Entry.EntryPre (NativeRustcVm.wordView m.dmem) ctx a bytes bytecode pub ∧
    Aligned a bytes.length bytecode.length ∧
    ApartFrom (entryRegions ctx a bytes.length bytecode.length) (stackBelow m leanvmVerifyStack)
      (leanvmVerifyStack + 8) ∧
    (∀ r ∈ entryRegions ctx a bytes.length bytecode.length, 0 < r.size → RodataApart r.addr r.size) ∧
    NativeRustcX64.GotAt m leanvmVerifyStack
      ((entryRegions ctx a bytes.length bytecode.length).map (fun r => (r.addr, r.size)) ++
        rodataAreas) ["memcpy", "memset"]

/-- The verdict: `1` when the wire bytes decode (`Proof.fromBytes`) to a proof `verifyWith`
accepts, else `0`. -/
def verdictWord (bytes : List UInt8) (bytecode : List UInt64) (pub : Vector UInt64 4) : UInt64 :=
  if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
      (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
    then 1 else 0

/-- `leanvm_verify`'s postcondition. -/
def LeanvmVerifyPost (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m m' : MachineData) : Prop :=
  reg m' .rax = (verdictWord bytes bytecode pub).toBitVec ∧
    SameOutside m.dmem m'.dmem (InAny [⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩,
      ⟨a.work.toBitVec, workAreaBytes⟩, frameR m leanvmVerifyStack]) ∧ Saved m m'

end

end

end NativeRustcVmX64
