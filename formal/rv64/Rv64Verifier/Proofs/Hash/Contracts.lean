import Rv64Verifier.Proofs.Hash.Mem
import Rv64Verifier.Proofs.Runtime.Memory
import Rv64Verifier.Image
import Rv64Verifier.Model.Hash

/-!
# Contracts of `memcpy`, `memset` and the Keccak functions

What a caller of these functions assumes, stated once here: `KeccakFSpec`, `XorBlockSpec` and
`KeccakHashSpec` are proved in `Proofs/Hash/` from the contracts of their callees, taken as
hypotheses; `MemcpySpec` and `MemsetSpec` follow from the runtime's (`Hash/All.lean`).

Bytes are what `lbu`/`sb` read and write (`MachineState.getByte`), in byte ranges whose bytes are
valid addresses (`BytesValid`), or that lie in one data window (the runtime's `Mapped`, what
`memcpy`, `memset` and `keccak_hash`'s data need); a contract's frame is stated on doublewords: memory changes only
in the doublewords meeting the ranges it names.
-/

namespace Rv64Verifier.Contracts
open RiscvZkvm.Rv64 Rv64Verifier.Model

/-- The `n` bytes from `a` are valid addresses, and do not wrap. -/
def BytesValid (a : Word) (n : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64 ∧ ∀ i < n, isValidMemAddr (a + BitVec.ofNat 64 i) = true

/-- The `n` bytes from `a`. -/
def bytesAt (s : MachineState) (a : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i ↦ s.getByte (a + BitVec.ofNat 64 i)

/-- Memory changes only in the doublewords meeting the `n` bytes from `lo`, and in the `m` bytes
from `lo'`. -/
def Frame2 (s t : MachineState) (lo : Word) (n : Nat) (lo' : Word) (m : Nat) : Prop :=
  ∀ a, Apart a 8 lo n → ¬ Within a lo' m → t.getMem a = s.getMem a

/-! ## `memcpy` and `memset` -/

/-- The stack bytes below `sp` that `memcpy` and `memset` may use. -/
@[rv_addr] def memStack : Nat := 16

/-- `a0` = `dst`, `a1` = `src`, `a2` = `n`: byte ranges in a data window, apart from each other
and from the stack. -/
structure MemcpyPre (s : MachineState) : Prop where
  dst : Runtime.Mapped (s.getReg .x10) (s.getReg .x12).toNat
  src : Runtime.Mapped (s.getReg .x11) (s.getReg .x12).toNat
  apart : Apart (s.getReg .x10) (s.getReg .x12).toNat (s.getReg .x11) (s.getReg .x12).toNat
  stack : StackOk s memStack
  dstStack : Apart (s.getReg .x10) (s.getReg .x12).toNat (stackLo s memStack) memStack
  srcStack : Apart (s.getReg .x11) (s.getReg .x12).toNat (stackLo s memStack) memStack

/-- The `n` bytes at `dst` are those at `src`; memory changes only in the doublewords meeting
`dst`'s bytes and the stack, and no byte outside them changes. -/
structure MemcpyPost (s t : MachineState) : Prop where
  bytes : bytesAt t (s.getReg .x10) (s.getReg .x12).toNat =
    bytesAt s (s.getReg .x11) (s.getReg .x12).toNat
  frame : Frame2 s t (s.getReg .x10) (s.getReg .x12).toNat (stackLo s memStack) memStack
  byteFrame : ∀ a, ¬ Within a (s.getReg .x10) (s.getReg .x12).toNat →
    ¬ Within a (stackLo s memStack) memStack → t.getByte a = s.getByte a

abbrev MemcpySpec : Prop := FunSpec Image.code 0x800126e4 MemcpyPre MemcpyPost

/-- `a0` = `dst`, `a1` = the byte, `a2` = `n`: a byte range in a data window, apart from the
stack. -/
structure MemsetPre (s : MachineState) : Prop where
  dst : Runtime.Mapped (s.getReg .x10) (s.getReg .x12).toNat
  stack : StackOk s memStack
  dstStack : Apart (s.getReg .x10) (s.getReg .x12).toNat (stackLo s memStack) memStack

/-- The `n` bytes at `dst` are `a1`'s low byte; memory changes only in the doublewords meeting
`dst`'s bytes and the stack, and no byte outside them changes. -/
structure MemsetPost (s t : MachineState) : Prop where
  bytes : bytesAt t (s.getReg .x10) (s.getReg .x12).toNat =
    List.replicate (s.getReg .x12).toNat ((s.getReg .x11).setWidth 8)
  frame : Frame2 s t (s.getReg .x10) (s.getReg .x12).toNat (stackLo s memStack) memStack
  byteFrame : ∀ a, ¬ Within a (s.getReg .x10) (s.getReg .x12).toNat →
    ¬ Within a (stackLo s memStack) memStack → t.getByte a = s.getByte a

abbrev MemsetSpec : Prop := FunSpec Image.code 0x800126f4 MemsetPre MemsetPost

/-! ## Keccak's tables -/

/-- `KECCAK_RHO` as the image holds it: `u32`s, two to a doubleword. -/
def keccakRhoWords : List Word :=
  (List.range 13).map fun j ↦ BitVec.ofNat 64 (keccakRhoRust.getD (2 * j) 0) |||
    BitVec.ofNat 64 (keccakRhoRust.getD (2 * j + 1) 0) <<< 32

/-- `KECCAK_RC`, `KECCAK_RHO` and `KECCAK_PI`, as the image holds them from `keccakTablesAddr`. -/
def keccakTableWords : List Word :=
  keccakRCRust ++ keccakRhoWords ++ keccakPiRust.map (BitVec.ofNat 64)

@[rv_addr] def keccakTablesAddr : Word := 0xa0000490

/-- The bytes of the tables. -/
@[rv_addr] def keccakTablesSize : Nat := 496

/-- The tables are in memory. -/
def KeccakTables (s : MachineState) : Prop :=
  s.readWords keccakTablesAddr 62 = keccakTableWords

/-- The loaded image holds the tables. -/
theorem keccakTables_of_data {s : MachineState} (h : ∀ p ∈ Image.dataWords, s.getMem p.1 = p.2) :
    KeccakTables s := by
  have hd : (List.range 62).all (fun i ↦ Image.dataWords.contains
      (keccakTablesAddr + BitVec.ofNat 64 (8 * i), keccakTableWords.getD i 0)) = true := by
    decide +kernel
  apply List.ext_getElem
  · rw [readWords_length]; rfl
  · intro i hi _
    rw [readWords_length] at hi
    have := List.all_eq_true.mp hd i (List.mem_range.mpr hi)
    rw [List.contains_iff_mem] at this
    rw [readWords_getElem _ _ _ _ hi, h _ this, List.getD_eq_getElem _ _ (by
      simp [keccakTableWords, keccakRhoWords, keccakRCRust, keccakPiRust]; omega)]

/-! ## `keccak_f` -/

/-- `keccak_f`'s frame and `memcpy`'s or `memset`'s below it. -/
@[rv_addr] def keccakFStack : Nat := 640 + memStack

/-- `a0` = the 25 lanes: valid, apart from the stack; the tables in memory, apart from both. -/
structure KeccakFPre (s : MachineState) : Prop where
  state : ValidMemRange (s.getReg .x10) 25
  stack : StackOk s keccakFStack
  stateStack : Apart (s.getReg .x10) 200 (stackLo s keccakFStack) keccakFStack
  tables : KeccakTables s
  tablesState : Apart keccakTablesAddr keccakTablesSize (s.getReg .x10) 200
  tablesStack : Apart keccakTablesAddr keccakTablesSize (stackLo s keccakFStack) keccakFStack

/-- The lanes are Keccak-f[1600] of the lanes (`keccakFRust_eq`); memory changes only in the lanes
and the stack. -/
structure KeccakFPost (s t : MachineState) : Prop where
  value : t.readWords (s.getReg .x10) 25 = keccakFRust (s.readWords (s.getReg .x10) 25)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 200 → ¬ Within a (stackLo s keccakFStack) keccakFStack →
    t.getMem a = s.getMem a

abbrev KeccakFSpec : Prop := FunSpec Image.code 0x80004210 KeccakFPre KeccakFPost

/-! ## `xor_block` -/

/-- `xor_block`'s frame. -/
@[rv_addr] def xorBlockStack : Nat := 512

/-- `a0` = the 25 lanes, `a1` = the block's 136 bytes: valid, apart from each other and from the
stack. -/
structure XorBlockPre (s : MachineState) : Prop where
  state : ValidMemRange (s.getReg .x10) 25
  block : BytesValid (s.getReg .x11) 136
  stack : StackOk s xorBlockStack
  stateStack : Apart (s.getReg .x10) 200 (stackLo s xorBlockStack) xorBlockStack
  blockStack : Apart (s.getReg .x11) 136 (stackLo s xorBlockStack) xorBlockStack
  stateBlock : Apart (s.getReg .x10) 200 (s.getReg .x11) 136

/-- The lanes are `xorBlockRust` of the lanes and the block; memory changes only in the lanes and
the stack. -/
structure XorBlockPost (s t : MachineState) : Prop where
  value : t.readWords (s.getReg .x10) 25 =
    xorBlockRust (s.readWords (s.getReg .x10) 25) (bytesAt s (s.getReg .x11) 136)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 200 → ¬ Within a (stackLo s xorBlockStack) xorBlockStack →
    t.getMem a = s.getMem a

abbrev XorBlockSpec : Prop := FunSpec Image.code 0x8000e5c8 XorBlockPre XorBlockPost

/-! ## `keccak_hash` -/

/-- `keccak_hash`'s frame and `keccak_f`'s stack below it, the deepest of its callees'. -/
@[rv_addr] def keccakHashStack : Nat := 448 + keccakFStack

/-- `a0` = where the digest goes (32 bytes, aligned), `a1`/`a2` = the data: in a data window,
apart from the stack; the tables in memory, apart from the stack. -/
structure KeccakHashPre (s : MachineState) : Prop where
  out : BytesValid (s.getReg .x10) 32
  outAligned : (s.getReg .x10).toNat % 8 = 0
  data : Runtime.Mapped (s.getReg .x11) (s.getReg .x12).toNat
  stack : StackOk s keccakHashStack
  outStack : Apart (s.getReg .x10) 32 (stackLo s keccakHashStack) keccakHashStack
  dataStack : Apart (s.getReg .x11) (s.getReg .x12).toNat (stackLo s keccakHashStack)
    keccakHashStack
  tables : KeccakTables s
  tablesStack : Apart keccakTablesAddr keccakTablesSize (stackLo s keccakHashStack) keccakHashStack

/-- The digest is `keccakHashRust` of the data (`keccakHashRust_eq`: Keccak-256); memory changes
only in the digest and the stack. -/
structure KeccakHashPost (s t : MachineState) : Prop where
  value : bytesAt t (s.getReg .x10) 32 =
    keccakHashRust (bytesAt s (s.getReg .x11) (s.getReg .x12).toNat)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 32 →
    ¬ Within a (stackLo s keccakHashStack) keccakHashStack → t.getMem a = s.getMem a

abbrev KeccakHashSpec : Prop := FunSpec Image.code 0x8000c8e0 KeccakHashPre KeccakHashPost

end Rv64Verifier.Contracts
