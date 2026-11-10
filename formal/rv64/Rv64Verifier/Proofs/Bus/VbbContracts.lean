import Rv64Verifier.Proofs.Bus.Contracts

/-!
# Callees of `verify_bus_balance` without a contract in this tree

`bus_layout` (`0x80010acc`), and `eq_kernel` (`0x8000cb38`) as the multilinear agent states it
(`Proofs/Multilinear/Contracts.lean`, `MultilinearContracts.EqKernelSpec`): on merging, this copy
gives way to that one.

A `BusLayout` (56 bytes) holds `framework: Vec<Placement>` at `+0`, `tables: Vec<Placement>` at
`+24` and `depth` at `+48`; a `Placement` (16 bytes) its `variables` at `+0` and `index` at `+8`
(read off `bus_layout`'s stores and `verify_bus_balance`'s loads).
-/

namespace Rv64Verifier.Bus
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.MultilinearContracts Rv64Verifier.Transcript

/-! ## `eq_kernel`, at `0x8000cb38` -/

namespace Vbb

/-- `eq_kernel`'s 208-byte frame and `mul`'s stack below it. -/
@[rv_addr] def eqKernelStack : Nat := 208 + Contracts.mulStack

/-- `a0` = where the `Vec` goes, `a1`/`a2` = the point, of fewer than `64` coordinates. -/
structure EqKernelPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  point : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  small : (s.getReg .x12).toNat < 64
  stack : Runtime.RtStack s eqKernelStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s eqKernelStack) eqKernelStack
  outRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize
  pointFree : Runtime.Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  pointStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s eqKernelStack)
    eqKernelStack
  pointOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  rodata : RodataOk s

/-- What `eq_kernel` may write: the result, the stack, `NEXT` and what it allocates. -/
@[rv_addr] def EqKernelW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s eqKernelStack) eqKernelStack ∨
    Within a Runtime.nextAddr 8 ∨ Runtime.Fresh s t a

/-- A new `Vec` of `eqKernelRust point`, its `2^n` elements freshly allocated. -/
structure EqKernelPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  vec : Runtime.VecOk t (s.getReg .x10) 24 8
  len : (Runtime.vecLen t (s.getReg .x10)).toNat = 2 ^ (s.getReg .x12).toNat
  elems : Runtime.vecEs t (s.getReg .x10) =
    Model.eqKernelRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat)
  fresh : Runtime.NewBuf s t (Runtime.vecPtr t (s.getReg .x10)) (24 * 2 ^ (s.getReg .x12).toNat) 8
  frame : ∀ a, (∀ i < 8, ¬ EqKernelW s t (a + BitVec.ofNat 64 i)) → t.getMem a = s.getMem a

abbrev EqKernelSpec : Prop := FunSpec Image.code 0x8000cb38 EqKernelPre EqKernelPost

end Vbb

/-! ## `bus_layout`, at `0x80010acc` -/

/-- Its 112-byte frame and `Vec<K>::reserve`'s stack below it, the deepest of its callees'
(`try_allocate_in`, `memcpy`, `stack_offsets`). -/
@[rv_addr] def busLayoutStack : Nat := 112 + reserveStack

/-- The blocks from `p`, `n` of them, 48 bytes apart. -/
def blocksFrom (s : MachineState) (p : Word) (n : Nat) : List BusBlock :=
  (List.range n).map fun i ↦ blockAt s (p + BitVec.ofNat 64 (48 * i))

theorem blocksAt_eq (s : MachineState) (a : Word) :
    blocksAt s a = blocksFrom s (vecPtr s a) (vecLen s a).toNat := rfl

/-- The `Vec<Placement>` at `a`. -/
def placementsAt (s : MachineState) (a : Word) : List PlacementRust :=
  (List.range (vecLen s a).toNat).map fun i ↦
    ⟨(s.getMem (vecPtr s a + BitVec.ofNat 64 (16 * i))).toNat,
      s.getMem (vecPtr s a + BitVec.ofNat 64 (16 * i) + 8)⟩

/-- The `BusLayout` at `a`. -/
def busLayoutOf (s : MachineState) (a : Word) : BusLayoutRust :=
  ⟨(s.getMem (a + 48)).toNat, placementsAt s a, placementsAt s (a + 24)⟩

/-- `bus_layout` reads the `m` bytes from `a`: valid, outside the free heap and `NEXT`, apart
from its stack and from the result at `out`. -/
structure LayoutRead (s : MachineState) (out a : Word) (m : Nat) : Prop where
  region : m = 0 ∨ Region a m
  free : Outside s a m
  stack : Apart a m (stackLo s busLayoutStack) busLayoutStack
  out : Apart a m out 56

/-- `a0` = where the `BusLayout` goes, `a1`/`a2` = `framework_log_rows`, `a3`/`a4` = the blocks. -/
structure BusLayoutPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s busLayoutStack
  out : Region (s.getReg .x10) 56
  outFree : Outside s (s.getReg .x10) 56
  outStack : Apart (s.getReg .x10) 56 (stackLo s busLayoutStack) busLayoutStack
  rows : LayoutRead s (s.getReg .x10) (s.getReg .x11) (8 * (s.getReg .x12).toNat)
  blocks : LayoutRead s (s.getReg .x10) (s.getReg .x13) (48 * (s.getReg .x14).toNat)

/-- `busLayoutRust` of the rows and the blocks, both `Vec`s' buffers new; memory changes only in
the result, the stack, `NEXT` and the heap allocated. -/
structure BusLayoutPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : busLayoutOf t (s.getReg .x10) =
    busLayoutRust (natsAt s (s.getReg .x11) (s.getReg .x12).toNat)
      (blocksFrom s (s.getReg .x13) (s.getReg .x14).toNat)
  framework : VecOk t (s.getReg .x10) 16 8 ∧
    NewBuf s t (vecPtr t (s.getReg .x10)) (16 * (vecCap t (s.getReg .x10)).toNat) 8
  tables : VecOk t (s.getReg .x10 + 24) 16 8 ∧
    NewBuf s t (vecPtr t (s.getReg .x10 + 24)) (16 * (vecCap t (s.getReg .x10 + 24)).toNat) 8
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 56 ∨
    Within a (stackLo s busLayoutStack) busLayoutStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev BusLayoutSpec : Prop := FunSpec Image.code 0x80010acc BusLayoutPre BusLayoutPost

end Rv64Verifier.Bus
