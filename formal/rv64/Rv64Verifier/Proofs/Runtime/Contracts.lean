import Rv64Verifier.Proofs.Runtime.Memory
import Rv64Verifier.Image

/-!
# Contracts of the runtime

The allocator, `RawVec`'s growth, the `mem*` builtins and the drop glue, as `FunSpec`s a caller
assumes (`Runtime/*.lean` prove them). Each says how many bytes below `sp` it may use, its callees'
included (`*Stack`), and which memory it may change: a `ByteFrame` (`Memory.lean`) of the bytes it
writes, the stack below `sp`, `NEXT` and what it allocates (`Fresh`).

A caller keeps the heap in shape (`HeapOk`), its stack above the heap (`RtStack`), and the data an
allocation must not touch outside the free heap (`Outside`). Allocating never fails: the allocator
halts with `2` instead (a `Dead` end), so the only error left to `RawVec` is a capacity overflow,
which its callers turn into a trap.
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64

/-! ## `Bump::alloc` (`guest/src/main.rs`), at `0x80000284` -/

@[rv_addr] def allocStack : Nat := 0

/-- `a0` = the alignment, `a1` = the size. -/
structure AllocPre (s : MachineState) : Prop where
  heap : HeapOk s
  align : 0 < (s.getReg .x10).toNat ∧ (s.getReg .x10).toNat ≤ 2 ^ 32

/-- `a0` = `NEXT` rounded up to the alignment, `NEXT` advanced past the `a1` bytes from there, and
nothing else written. -/
structure AllocPost (s t : MachineState) : Prop where
  aligned : (t.getReg .x10).toNat % (s.getReg .x10).toNat = 0
  above : heapNext s ≤ (t.getReg .x10).toNat
  next : heapNext t = (t.getReg .x10).toNat + (s.getReg .x11).toNat
  heap : HeapOk t
  mem : ∀ a, a ≠ nextAddr → t.getMem a = s.getMem a

def AllocSpec : Prop := FunSpec Image.code 0x80000284 AllocPre AllocPost

/-! ## `RawVecInner::try_allocate_in`, at `0x80000024` (uninitialized) and `0x800049ac` -/

@[rv_addr] def tryAllocStack : Nat := 48

/-- `a0` = where the `Result<RawVecInner, TryReserveError>` goes, `a1` = the capacity, then the
alignment and the element size (`a2`, `a3` at `0x80000024`; `a3`, `a4` at `0x800049ac`, whose `a2`
says whether to zero the buffer). -/
structure TryAllocPre (al sz : Reg) (s : MachineState) : Prop where
  heap : HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  align : 0 < (s.getReg al).toNat ∧ (s.getReg al).toNat ≤ 2 ^ 32
  size : 0 < (s.getReg sz).toNat
  stack : RtStack s tryAllocStack
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s tryAllocStack) tryAllocStack

/-- `Ok` (tag `0` at `a0`): the capacity at `a0 + 8`, a new buffer of that many elements at
`a0 + 16`; for capacity 0, the dangling pointer `align`. -/
structure TryAllocPost (al sz : Reg) (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : t.getMem (s.getReg .x10) = 0 → t.getMem (s.getReg .x10 + 8) = s.getReg .x11 ∧
    NewBuf s t (t.getMem (s.getReg .x10 + 16)) ((s.getReg .x11).toNat * (s.getReg sz).toNat)
      (s.getReg al).toNat
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s tryAllocStack) tryAllocStack ∨ Within a nextAddr 8 ∨ Fresh s t a
  dangling : t.getMem (s.getReg .x10) = 0 → s.getReg .x11 = 0 →
    t.getMem (s.getReg .x10 + 16) = s.getReg al

def TryAllocSpec : Prop := FunSpec Image.code 0x80000024 (TryAllocPre .x12 .x13) (TryAllocPost .x12 .x13)

/-- With `a2 ≠ 0`, the buffer is zeroed. -/
def TryAllocZeroedSpec : Prop := FunSpec Image.code 0x800049ac (TryAllocPre .x13 .x14) fun s t ↦
  TryAllocPost .x13 .x14 s t ∧ (s.getReg .x12 ≠ 0 → t.getMem (s.getReg .x10) = 0 →
    bytesAt t (t.getMem (s.getReg .x10 + 16)) ((s.getReg .x11).toNat * (s.getReg .x14).toNat) =
      List.replicate ((s.getReg .x11).toNat * (s.getReg .x14).toNat) 0)

/-- An empty buffer's dangling pointer, its alignment, lies below the heap. -/
theorem dangling_lt_heap {align : Nat} (h : align ≤ 16) :
    (BitVec.ofNat 64 align).toNat < heapStart := by
  simp only [BitVec.toNat_ofNat, heapStart]
  omega

/-- The dangling pointer, as an empty range, misses the free heap and `NEXT`, and lies below
`NEXT`. -/
theorem dangling_outside {s : MachineState} {align : Nat} (hs : HeapOk s) (h : align ≤ 16) :
    Outside s (BitVec.ofNat 64 align) 0 ∧ (BitVec.ofNat 64 align).toNat < heapNext s := by
  have h1 := dangling_lt_heap h
  have h2 := hs.lo
  exact ⟨⟨Or.inl (by omega), Or.inl rfl⟩, by omega⟩

/-! ## `RawVecInner::finish_grow`, at `0x8000c224` -/

@[rv_addr] def finishGrowStack : Nat := 96

/-- `a0` = where the `Result<NonNull<[u8]>, TryReserveError>` goes, `a1`, `a2` = the old capacity
and buffer, `a3` = the new capacity, `a4` = the alignment, `a5` = the element size. -/
structure FinishGrowPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  align : 0 < (s.getReg .x14).toNat ∧ (s.getReg .x14).toNat ≤ 2 ^ 32
  size : 0 < (s.getReg .x15).toNat
  old : Buf s (s.getReg .x12) ((s.getReg .x11).toNat * (s.getReg .x15).toNat) (s.getReg .x14).toNat
  le : (s.getReg .x11).toNat ≤ (s.getReg .x13).toNat
  stack : RtStack s finishGrowStack
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s finishGrowStack) finishGrowStack
  outOld : Apart (s.getReg .x10) 24 (s.getReg .x12) ((s.getReg .x11).toNat * (s.getReg .x15).toNat)

/-- `Ok` (tag `0`): a new buffer for the new capacity at `a0 + 8`, starting with the old one's
bytes. The only error (tag `1`) is a capacity overflow, `0` at `a0 + 8`. -/
structure FinishGrowPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : t.getMem (s.getReg .x10) = 0 →
    NewBuf s t (t.getMem (s.getReg .x10 + 8)) ((s.getReg .x13).toNat * (s.getReg .x15).toNat)
      (s.getReg .x14).toNat ∧
    bytesAt t (t.getMem (s.getReg .x10 + 8)) ((s.getReg .x11).toNat * (s.getReg .x15).toNat) =
      bytesAt s (s.getReg .x12) ((s.getReg .x11).toNat * (s.getReg .x15).toNat)
  err : t.getMem (s.getReg .x10) ≠ 0 → t.getMem (s.getReg .x10 + 8) = 0
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s finishGrowStack) finishGrowStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def FinishGrowSpec : Prop := FunSpec Image.code 0x8000c224 FinishGrowPre FinishGrowPost

/-! ## `RawVecInner::grow_amortized`, at `0x8000c184` -/

@[rv_addr] def growStack : Nat := 144

/-- `a0` = the `RawVec`, `a1` = the length, `a2` = how many more, `a3` = the alignment, `a4` =
the element size. -/
structure GrowPre (s : MachineState) : Prop where
  heap : HeapOk s
  self : ValidMemRange (s.getReg .x10) 2
  align : 0 < (s.getReg .x13).toNat ∧ (s.getReg .x13).toNat ≤ 2 ^ 32
  size : 0 < (s.getReg .x14).toNat
  raw : RawVecOk s (s.getReg .x10) (s.getReg .x14).toNat (s.getReg .x13).toNat
  stack : RtStack s growStack
  selfFree : Outside s (s.getReg .x10) 16
  selfStack : Apart (s.getReg .x10) 16 (stackLo s growStack) growStack

/-- `Ok` (`a0 = -1`): room for `len + additional`, a new buffer starting with the old one's
bytes. -/
structure GrowPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : t.getReg .x10 = 0xffffffffffffffff →
    (s.getReg .x11).toNat + (s.getReg .x12).toNat ≤ (vecCap t (s.getReg .x10)).toNat ∧
    RawVecOk t (s.getReg .x10) (s.getReg .x14).toNat (s.getReg .x13).toNat ∧
    bytesAt t (vecPtr t (s.getReg .x10)) ((vecCap s (s.getReg .x10)).toNat * (s.getReg .x14).toNat) =
      bytesAt s (vecPtr s (s.getReg .x10)) ((vecCap s (s.getReg .x10)).toNat * (s.getReg .x14).toNat)
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 16 ∨
    Within a (stackLo s growStack) growStack ∨ Within a nextAddr 8 ∨ Fresh s t a
  /-- On `Ok`, the buffer is a new one. -/
  fresh : t.getReg .x10 = 0xffffffffffffffff →
    NewBuf s t (vecPtr t (s.getReg .x10))
      ((vecCap t (s.getReg .x10)).toNat * (s.getReg .x14).toNat) (s.getReg .x13).toNat

def GrowSpec : Prop := FunSpec Image.code 0x8000c184 GrowPre GrowPost

/-! ## `RawVec<T>::grow_one`

One copy per element type, the same code with the type's size and alignment: at `0x8000c0a4`
(`ColumnClaim`, 56 bytes), `0x8000c7d0` (`(Vec<E>, GluedWeight)`, 80), `0x8000d7bc` (`K`, 8),
`0x8000db78` (`GluedClaim`, 88), `0x80010a94` (`(Vec<E>, Vec<E>)`, 48), `0x80011c78`
(`Vec<Form>`, 24), all aligned to 8, `0x80011f88` (`u16`, 2, aligned to 2) and `0x80011fc0`
(`(u64, usize)`, 16). -/

@[rv_addr] def growOneStack : Nat := 160

/-- `a0` = the `RawVec`. -/
structure GrowOnePre (size align : Nat) (s : MachineState) : Prop where
  heap : HeapOk s
  self : ValidMemRange (s.getReg .x10) 2
  raw : RawVecOk s (s.getReg .x10) size align
  stack : RtStack s growOneStack
  selfFree : Outside s (s.getReg .x10) 16
  selfStack : Apart (s.getReg .x10) 16 (stackLo s growOneStack) growOneStack

/-- One more element of room, a buffer starting with the old one's bytes. -/
structure GrowOnePost (size align : Nat) (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  cap : (vecCap s (s.getReg .x10)).toNat + 1 ≤ (vecCap t (s.getReg .x10)).toNat
  raw : RawVecOk t (s.getReg .x10) size align
  bytes : bytesAt t (vecPtr t (s.getReg .x10)) ((vecCap s (s.getReg .x10)).toNat * size) =
    bytesAt s (vecPtr s (s.getReg .x10)) ((vecCap s (s.getReg .x10)).toNat * size)
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 16 ∨
    Within a (stackLo s growOneStack) growOneStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def GrowOneSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (GrowOnePre size align) (GrowOnePost size align)

/-- `grow_one` whose new buffer is new. -/
def GrowOneFreshSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (GrowOnePre size align) fun s t ↦ GrowOnePost size align s t ∧
    NewBuf s t (vecPtr t (s.getReg .x10)) ((vecCap t (s.getReg .x10)).toNat * size) align

/-! ## `Vec<T>::reserve`

At `0x80004aec` (`Form`, 24 bytes), `0x800060bc` (`BusBlock`, 48), `0x80008a10` (`E`, 24),
`0x8000d628` (`K`, 8), `0x8001086c` (`Option<E>`, 32), all aligned to 8, and `0x8000c898` (`u8`,
1, aligned to 1). -/

@[rv_addr] def reserveStack : Nat := 160

/-- `a0` = the `Vec`, `a1` = how many more. -/
structure ReservePre (size align : Nat) (s : MachineState) : Prop where
  heap : HeapOk s
  self : ValidMemRange (s.getReg .x10) 3
  vec : VecOk s (s.getReg .x10) size align
  stack : RtStack s reserveStack
  selfFree : Outside s (s.getReg .x10) 24
  selfStack : Apart (s.getReg .x10) 24 (stackLo s reserveStack) reserveStack

/-- Room for `len + additional`, the same length, a buffer starting with the old one's bytes. -/
structure ReservePost (size align : Nat) (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  cap : (vecLen s (s.getReg .x10)).toNat + (s.getReg .x11).toNat ≤ (vecCap t (s.getReg .x10)).toNat
  vec : VecOk t (s.getReg .x10) size align
  len : vecLen t (s.getReg .x10) = vecLen s (s.getReg .x10)
  bytes : bytesAt t (vecPtr t (s.getReg .x10)) ((vecCap s (s.getReg .x10)).toNat * size) =
    bytesAt s (vecPtr s (s.getReg .x10)) ((vecCap s (s.getReg .x10)).toNat * size)
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 16 ∨
    Within a (stackLo s reserveStack) reserveStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def ReserveSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (ReservePre size align) (ReservePost size align)

/-- `reserve` whose buffer afterwards is the same one, or a new one: a `Vec` filled after the call
writes only memory allocated since. -/
def ReserveFreshSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (ReservePre size align) fun s t ↦ ReservePost size align s t ∧
    ((vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10) ∧
      vecCap t (s.getReg .x10) = vecCap s (s.getReg .x10)) ∨
     NewBuf s t (vecPtr t (s.getReg .x10)) ((vecCap t (s.getReg .x10)).toNat * size) align)

/-- `reserve` with room enough: it returns at once, writing nothing. -/
def ReserveFastSpec (entry : Word) : Prop :=
  FunSpec Image.code entry (fun s ↦ ValidMemRange (s.getReg .x10) 3 ∧
    (vecLen s (s.getReg .x10)).toNat + (s.getReg .x11).toNat ≤ (vecCap s (s.getReg .x10)).toNat)
    fun s t ↦ t.getReg .x10 = s.getReg .x10 ∧ ∀ a, t.getMem a = s.getMem a

/-- A weaker postcondition. -/
theorem _root_.Rv64Verifier.FunSpec.weaken {code : Code} {entry : Word}
    {P : MachineState → Prop} {Q Q' : MachineState → MachineState → Prop}
    (h : FunSpec code entry P Q) (hq : ∀ s t, Q s t → Q' s t) : FunSpec code entry P Q' :=
  fun s hpc hp ↦ (h s hpc hp).imp fun t ⟨hr, ht⟩ ↦ ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, hq s t c⟩⟩

/-! ## `compiler_builtins`: `memcpy` (`0x80011ff8`, called through `0x800126e4`), `memset`
(`0x800121f4`, through `0x800126f4`), `memmove` (`0x8001228c`, through `0x800126ec`), `memcmp`
(`0x800126b4`) -/

@[rv_addr] def memcpyStack : Nat := 16

/-- `a0` = the destination, `a1` = the source, `a2` = the length: mapped, apart from each other
and from the stack. -/
structure MemcpyPre (s : MachineState) : Prop where
  dst : Mapped (s.getReg .x10) (s.getReg .x12).toNat
  src : Mapped (s.getReg .x11) (s.getReg .x12).toNat
  apart : Apart (s.getReg .x10) (s.getReg .x12).toNat (s.getReg .x11) (s.getReg .x12).toNat
  stack : StackOk s memcpyStack
  dstStack : Apart (s.getReg .x10) (s.getReg .x12).toNat (stackLo s memcpyStack) memcpyStack
  srcStack : Apart (s.getReg .x11) (s.getReg .x12).toNat (stackLo s memcpyStack) memcpyStack

/-- The destination holds the source's bytes; `a0` is the destination. -/
structure MemcpyPost (s t : MachineState) : Prop where
  ret : t.getReg .x10 = s.getReg .x10
  bytes : bytesAt t (s.getReg .x10) (s.getReg .x12).toNat =
    bytesAt s (s.getReg .x11) (s.getReg .x12).toNat
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) (s.getReg .x12).toNat ∨
    Within a (stackLo s memcpyStack) memcpyStack

def MemcpySpec (entry : Word) : Prop := FunSpec Image.code entry MemcpyPre MemcpyPost

@[rv_addr] def memmoveStack : Nat := 16

/-- `memmove`: as `memcpy`, the ranges may overlap. -/
structure MemmovePre (s : MachineState) : Prop where
  dst : Mapped (s.getReg .x10) (s.getReg .x12).toNat
  src : Mapped (s.getReg .x11) (s.getReg .x12).toNat
  stack : StackOk s memmoveStack
  dstStack : Apart (s.getReg .x10) (s.getReg .x12).toNat (stackLo s memmoveStack) memmoveStack
  srcStack : Apart (s.getReg .x11) (s.getReg .x12).toNat (stackLo s memmoveStack) memmoveStack

def MemmoveSpec (entry : Word) : Prop := FunSpec Image.code entry MemmovePre MemcpyPost

@[rv_addr] def memsetStack : Nat := 0

/-- `a0` = the destination, `a1` = the byte (its low eight bits), `a2` = the length. -/
def MemsetPre (s : MachineState) : Prop := Mapped (s.getReg .x10) (s.getReg .x12).toNat

structure MemsetPost (s t : MachineState) : Prop where
  ret : t.getReg .x10 = s.getReg .x10
  bytes : bytesAt t (s.getReg .x10) (s.getReg .x12).toNat =
    List.replicate (s.getReg .x12).toNat ((s.getReg .x11).truncate 8)
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) (s.getReg .x12).toNat

def MemsetSpec (entry : Word) : Prop := FunSpec Image.code entry MemsetPre MemsetPost

/-- `memcmp`'s result on two byte lists: the difference of the first bytes that differ, zero if
none does. -/
def cmpBytes : List (BitVec 8) → List (BitVec 8) → Word
  | x :: xs, y :: ys => if x = y then cmpBytes xs ys else x.zeroExtend 64 - y.zeroExtend 64
  | _, _ => 0

/-- `a0`, `a1` = the two ranges, `a2` = the length. -/
structure MemcmpPre (s : MachineState) : Prop where
  lhs : Mapped (s.getReg .x10) (s.getReg .x12).toNat
  rhs : Mapped (s.getReg .x11) (s.getReg .x12).toNat

structure MemcmpPost (s t : MachineState) : Prop where
  ret : t.getReg .x10 = cmpBytes (bytesAt s (s.getReg .x10) (s.getReg .x12).toNat)
    (bytesAt s (s.getReg .x11) (s.getReg .x12).toNat)
  mem : ∀ a, t.getMem a = s.getMem a

def MemcmpSpec : Prop := FunSpec Image.code 0x800126b4 MemcmpPre MemcmpPost

/-! ## Drop glue -/

/-- `drop_glue::<Vec<Vec<Form>>>` at `0x8000c0dc`, a `ret`: dropping frees nothing. -/
def DropNopSpec : Prop :=
  FunSpec Image.code 0x8000c0dc (fun _ ↦ True) fun s t ↦ ∀ a, t.getMem a = s.getMem a

@[rv_addr] def dropLayoutStack : Nat := 32

/-- `drop_glue::<Layout>` at `0x8000c0e0`: `a0` = the `Layout`, whose first field is a `Vec` of
80-byte elements; it reads twelve doublewords of the `Layout` and four of each element. -/
structure DropLayoutPre (s : MachineState) : Prop where
  self : ValidMemRange (s.getReg .x10) 12
  elems : ValidMemRange (vecPtr s (s.getReg .x10)) (10 * (vecLen s (s.getReg .x10)).toNat)
  stack : StackOk s dropLayoutStack
  selfStack : Apart (s.getReg .x10) 96 (stackLo s dropLayoutStack) dropLayoutStack

def DropLayoutSpec : Prop :=
  FunSpec Image.code 0x8000c0e0 DropLayoutPre fun s t ↦
    MemFrame s t (stackLo s dropLayoutStack) dropLayoutStack

end Rv64Verifier.Runtime
