module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVm.RodataLemmas
public import NativeRustcArm.Spec.Keccak

/-!
# The read-only data of `leanvm_verify`'s AArch64 program

Each item of `NativeRustcVmArm.Vm.rodata` is at its label (`itemLabel`, `rodataAddr`).
`RodataAt m n` says every item's bytes are there, not wrapping around, apart from the `n` bytes
below SP: the precondition of a function reading the data. The labels, by the arrays rustc made
them of (matched by their bytes against `rustc/vm/src/data.rs`, and by the code addressing them):

| label `.Lanon.a75d6d9e6a8990b4224ef13f18552af8.` | array | read by |
|---|---|---|
| `0` | `RMFE_PROJECT` | `verify_layer` |
| `1` | `KECCAK_RC` | `keccak_f`, `verify_layer` |
| `2` | `KECCAK_RHO` | `linear_transpose` |
| `3` | `TUPLES` | `block_form` |
| `4` | `TABLES` | `accumulate_side`, `table_terms` |
| `5` | `PADDING` | `accumulate_side` |
| `6` | `PUSH_BLOCKS` | `verify_bus_balance` |
| `7` | `PULL_BLOCKS` | `verify_bus_balance` |
| `8` | `COUNT_BLOCKS` | `verify_bus_balance` |
| `9` | `&[ONE]` (`bus.rs`) | `verify_bus_balance` |
| `10` | `PER_CHALLENGE` (`whir.rs`) | `sample_queries` |
| `11` | `QUERY_TABLE` | `ladder` |
| `12` | `QUERY_LEVELS` | `ladder` |
| `13` | `FORMS` | `form_terms` |
| `14` | `TERMS` | `form_terms` |
| `15` | `KECCAK_SLOT` | `placements_of` |
| `16` | `KECCAK_OUTPUT` | `placements_of` |

That the program's data is exactly these bytes: `NativeRustcVmArm.Rodata.items_eq`
(`NativeRustcVmArm/Rodata/Items.lean`).
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeRustcVm.Data

@[expose] public section

/-- Each item's label in the AArch64 program. -/
def itemLabel : Item → Label
  | .rmfeProject => NativeRustcVmArm.Vm.Symbols.rodata0Label
  | .keccakRC => NativeRustcVmArm.Vm.Symbols.rodata1Label
  | .keccakRho => NativeRustcVmArm.Vm.Symbols.rodata2Label
  | .tuples => NativeRustcVmArm.Vm.Symbols.rodata3Label
  | .tables => NativeRustcVmArm.Vm.Symbols.rodata4Label
  | .padding => NativeRustcVmArm.Vm.Symbols.rodata5Label
  | .pushBlocks => NativeRustcVmArm.Vm.Symbols.rodata6Label
  | .pullBlocks => NativeRustcVmArm.Vm.Symbols.rodata7Label
  | .countBlocks => NativeRustcVmArm.Vm.Symbols.rodata8Label
  | .one => NativeRustcVmArm.Vm.Symbols.rodata9Label
  | .perChallenge => NativeRustcVmArm.Vm.Symbols.rodata10Label
  | .queryTable => NativeRustcVmArm.Vm.Symbols.rodata11Label
  | .queryLevels => NativeRustcVmArm.Vm.Symbols.rodata12Label
  | .forms => NativeRustcVmArm.Vm.Symbols.rodata13Label
  | .terms => NativeRustcVmArm.Vm.Symbols.rodata14Label
  | .keccakSlot => NativeRustcVmArm.Vm.Symbols.rodata15Label
  | .keccakOutput => NativeRustcVmArm.Vm.Symbols.rodata16Label

section
variable [Labels]

/-- An item's address: its label's. -/
def rodataAddr (t : Item) : BitVec 64 := (label (itemLabel t)).toBitVec

/-- **The read-only data at its labels**, apart from the `n` bytes below SP. -/
def RodataAt (m : MachineData) (n : Nat) : Prop :=
  NativeRustcVm.RodataAt m.dmem rodataAddr (stackBelow m n) n

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
    NativeRustcVm.Apart (rodataAddr t) t.bytes.length (stackBelow m n) n :=
  NativeRustcVm.RodataAt.apart h t

/-- The data stays at its labels in a state whose memory changed only in the stack, apart from a
stack range inside the first. -/
theorem mono {m' : MachineData} {n' : Nat} (h : RodataAt m n)
    (hs : NativeRustcVm.SameOutside m.dmem m'.dmem (NativeRustcVm.InRange (stackBelow m n) n))
    (hsb : NativeRustcVm.NoWrap (stackBelow m n) n)
    (h1 : (stackBelow m n).toNat ≤ (stackBelow m' n').toNat)
    (h2 : (stackBelow m' n').toNat + n' ≤ (stackBelow m n).toNat + n) : RodataAt m' n' :=
  NativeRustcVm.RodataAt.mono (NativeRustcVm.RodataAt.of_sameOutside h hs hsb) h1 h2

/-- The data stays at its labels in a state of the same memory, apart from a stack range inside
the first. -/
theorem mono_of_dmem {m' : MachineData} {n' : Nat} (h : RodataAt m n) (hd : m'.dmem = m.dmem)
    (h1 : (stackBelow m n).toNat ≤ (stackBelow m' n').toNat)
    (h2 : (stackBelow m' n').toNat + n' ≤ (stackBelow m n).toNat + n) : RodataAt m' n' := by
  have : NativeRustcVm.RodataAt m'.dmem rodataAddr (stackBelow m n) n := hd ▸ h
  exact NativeRustcVm.RodataAt.mono this h1 h2

end

end RodataAt

end NativeRustcVmArm
