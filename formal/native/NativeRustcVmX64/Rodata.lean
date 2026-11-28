module

public import NativeRustcVm.RodataLemmas
public import NativeRustcX64.Spec.Keccak
public import NativeRustcVmX64.Code.Vm.Names

/-!
# The read-only data of `leanvm_verify`'s x86-64 program

Each item of `NativeRustcVmX64.Vm.rodata` is at its label (`itemLabel`, `rodataAddr`).
`RodataAt m n` says every item's bytes are there, not wrapping around, apart from the `n` bytes
below RSP and the return address at RSP (the `n + 8` bytes from `stackBelow m n`, those `StackOk`
maps): the precondition of a function reading the data. The program's read-only data is the
AArch64 program's, directive for directive, so the labels are the same arrays
(`NativeRustcVmArm.itemLabel`'s table):

| label `.Lanon.a75d6d9e6a8990b4224ef13f18552af8.` | array |
|---|---|
| `0` | `RMFE_PROJECT` |
| `1` | `KECCAK_RC` |
| `2` | `KECCAK_RHO` |
| `3` | `TUPLES` |
| `4` | `TABLES` |
| `5` | `PADDING` |
| `6` | `PUSH_BLOCKS` |
| `7` | `PULL_BLOCKS` |
| `8` | `COUNT_BLOCKS` |
| `9` | `&[ONE]` (`bus.rs`) |
| `10` | `PER_CHALLENGE` (`whir.rs`) |
| `11` | `QUERY_TABLE` |
| `12` | `QUERY_LEVELS` |
| `13` | `FORMS` |
| `14` | `TERMS` |
| `15` | `KECCAK_SLOT` |
| `16` | `KECCAK_OUTPUT` |

That the program's data is exactly these bytes: `NativeRustcVmX64.Rodata.data_eq`
(`NativeRustcVmX64/Rodata/Items.lean`).
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeRustcVm.Data

@[expose] public section

/-- Each item's label in the x86-64 program. -/
def itemLabel : Item → Label
  | .rmfeProject => NativeRustcVmX64.Vm.Symbols.rodata0Label
  | .keccakRC => NativeRustcVmX64.Vm.Symbols.rodata1Label
  | .keccakRho => NativeRustcVmX64.Vm.Symbols.rodata2Label
  | .tuples => NativeRustcVmX64.Vm.Symbols.rodata3Label
  | .tables => NativeRustcVmX64.Vm.Symbols.rodata4Label
  | .padding => NativeRustcVmX64.Vm.Symbols.rodata5Label
  | .pushBlocks => NativeRustcVmX64.Vm.Symbols.rodata6Label
  | .pullBlocks => NativeRustcVmX64.Vm.Symbols.rodata7Label
  | .countBlocks => NativeRustcVmX64.Vm.Symbols.rodata8Label
  | .one => NativeRustcVmX64.Vm.Symbols.rodata9Label
  | .perChallenge => NativeRustcVmX64.Vm.Symbols.rodata10Label
  | .queryTable => NativeRustcVmX64.Vm.Symbols.rodata11Label
  | .queryLevels => NativeRustcVmX64.Vm.Symbols.rodata12Label
  | .forms => NativeRustcVmX64.Vm.Symbols.rodata13Label
  | .terms => NativeRustcVmX64.Vm.Symbols.rodata14Label
  | .keccakSlot => NativeRustcVmX64.Vm.Symbols.rodata15Label
  | .keccakOutput => NativeRustcVmX64.Vm.Symbols.rodata16Label

section
variable [Labels]

/-- An item's address: its label's. -/
def rodataAddr (t : Item) : BitVec 64 := (label (itemLabel t)).toBitVec

/-- The read-only regions reached by the VM verifier. -/
def rodataAreas : List (BitVec 64 × Nat) :=
  Item.all.map fun t => (rodataAddr t, t.bytes.length)

/-- **The read-only data at its labels**, apart from the `n` bytes below RSP and the return
address at RSP. -/
def RodataAt (m : MachineData) (n : Nat) : Prop :=
  NativeRustcVm.RodataAt m.dmem rodataAddr (stackBelow m n) (n + 8)

/-- The `n` bytes from `a` are apart from every item of the read-only data. -/
def RodataApart (a : BitVec 64) (n : Nat) : Prop := NativeRustcVm.RodataApart rodataAddr a n

end

end

namespace RodataAt

public section

variable [Labels] {m : MachineData} {n : Nat}

theorem bytesAt (h : RodataAt m n) (t : Item) :
    NativeRustcVm.BytesAt m.dmem (rodataAddr t) t.bytes :=
  NativeRustcVm.RodataAt.bytesAt h t

theorem noWrap (h : RodataAt m n) (t : Item) : NativeRustcVm.NoWrap (rodataAddr t) t.bytes.length :=
  NativeRustcVm.RodataAt.noWrap h t

theorem apart (h : RodataAt m n) (t : Item) :
    NativeRustcVm.Apart (rodataAddr t) t.bytes.length (stackBelow m n) (n + 8) :=
  NativeRustcVm.RodataAt.apart h t

/-- The data stays at its labels in a state whose memory changed only in the stack, apart from a
stack range inside the first. -/
theorem mono {m' : MachineData} {n' : Nat} (h : RodataAt m n)
    (hs : NativeRustcVm.SameOutside m.dmem m'.dmem
      (NativeRustcVm.InRange (stackBelow m n) (n + 8)))
    (hsb : NativeRustcVm.NoWrap (stackBelow m n) (n + 8))
    (h1 : (stackBelow m n).toNat ≤ (stackBelow m' n').toNat)
    (h2 : (stackBelow m' n').toNat + (n' + 8) ≤ (stackBelow m n).toNat + (n + 8)) :
    RodataAt m' n' :=
  NativeRustcVm.RodataAt.mono (NativeRustcVm.RodataAt.of_sameOutside h hs hsb) h1 h2

/-- The data stays at its labels in a state of the same memory, apart from a stack range inside
the first. -/
theorem mono_of_dmem {m' : MachineData} {n' : Nat} (h : RodataAt m n) (hd : m'.dmem = m.dmem)
    (h1 : (stackBelow m n).toNat ≤ (stackBelow m' n').toNat)
    (h2 : (stackBelow m' n').toNat + (n' + 8) ≤ (stackBelow m n).toNat + (n + 8)) :
    RodataAt m' n' := by
  have : NativeRustcVm.RodataAt m'.dmem rodataAddr (stackBelow m n) (n + 8) := hd ▸ h
  exact NativeRustcVm.RodataAt.mono this h1 h2

end

end RodataAt

end NativeRustcVmX64
