import Rv64Verifier.Proofs.Bus.Contracts

/-!
# Callees of `verify_bus_balance` without a contract in this tree

`bus_layout` (`0x80010acc`), `eq_kernel` (`0x8000cb38`) as the multilinear agent states it
(`Proofs/Multilinear/Contracts.lean`, `MultilinearContracts.EqKernelSpec`; on merging, this copy
gives way to that one), `multilinear_eval::<E>` (`0x8000d28c`) and `Bytecode::evaluate`
(`0x80010e24`). The last reads the `Bytecode` through a predicate `BcOk` left abstract here (the
bytecode agent's contract says what it is); `bev` is what it computes.

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
  out : Region (s.getReg .x10) 24
  point : (s.getReg .x12).toNat = 0 ∨ Region (s.getReg .x11) (24 * (s.getReg .x12).toNat)
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

/-! ## `multilinear_eval::<E>`, at `0x8000d28c` -/

namespace Vbb

/-- Its 208-byte frame and `mul`'s stack below it, the deepest of its callees' (`try_allocate_in`,
`reserve`, `Scaler::new`, `mul`, `memcpy`). -/
@[rv_addr] def mleEvalStack : Nat := 208 + Contracts.mulStack

/-- `a0` = the `Result<E, VerifierError>` (tag, then the value), `a1`/`a2` = the evaluations,
`a3`/`a4` = the point; both read only. -/
structure MleEvalPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  stack : Runtime.RtStack s mleEvalStack
  rodata : RodataOk s
  out : Region (s.getReg .x10) 32
  outFree : Runtime.Outside s (s.getReg .x10) 32
  outStack : Apart (s.getReg .x10) 32 (stackLo s mleEvalStack) mleEvalStack
  outRodata : Apart (s.getReg .x10) 32 rodataBase rodataSize
  mle : Held s mleEvalStack (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  mleOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 32
  point : Held s mleEvalStack (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  pointOut : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (s.getReg .x10) 32

/-- `Ok` (tag `0`) with `multilinearEvalRust`'s value when it has one, otherwise `Err`; memory
changes only in the result, the stack, `NEXT` and the heap allocated. -/
structure MleEvalPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  value : match multilinearEvalRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat)
      (eListAt s (s.getReg .x13) (s.getReg .x14).toNat) with
    | some v => t.getMem (s.getReg .x10) = 0 ∧ eAt t (s.getReg .x10 + 8) = v
    | none => t.getMem (s.getReg .x10) ≠ 0
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨
    Within a (stackLo s mleEvalStack) mleEvalStack ∨ Within a Runtime.nextAddr 8 ∨
    Runtime.Fresh s t a

abbrev MleEvalSpec : Prop := FunSpec Image.code 0x8000d28c MleEvalPre MleEvalPost

/-! ## `Bytecode::evaluate`, at `0x80010e24` -/

/-- Its 1968-byte frame and `eq_kernel`'s stack below it. -/
@[rv_addr] def bytecodeEvalStack : Nat := 1968 + eqKernelStack

/-- `a0` = the `Result<E, VerifierError>` in the caller's frame, `a1` = the `Bytecode` (as `BcOk`
says, for a callee with an `n`-byte stack), `a2`/`a3` = the point, read only. -/
structure BytecodeEvalPre (BcOk : MachineState → Nat → Word → Prop) (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  stack : Runtime.RtStack s bytecodeEvalStack
  rodata : RodataOk s
  out : Region (s.getReg .x10) 32
  outFree : Runtime.Outside s (s.getReg .x10) 32
  outStack : Apart (s.getReg .x10) 32 (stackLo s bytecodeEvalStack) bytecodeEvalStack
  outRodata : Apart (s.getReg .x10) 32 rodataBase rodataSize
  bytecode : BcOk s bytecodeEvalStack (s.getReg .x11)
  /-- The result lies in the caller's frame, right above the callee's stack. -/
  outFrame : (stackLo s bytecodeEvalStack).toNat ≤ (s.getReg .x10).toNat ∧
    (s.getReg .x10).toNat + 32 ≤ (stackLo s bytecodeEvalStack).toNat + busBalanceStack
  point : Held s bytecodeEvalStack (s.getReg .x12) (24 * (s.getReg .x13).toNat)
  pointOut : Apart (s.getReg .x12) (24 * (s.getReg .x13).toNat) (s.getReg .x10) 32

/-- `Ok` with `bev`'s value when it has one, otherwise `Err`. -/
structure BytecodeEvalPost (bev : MachineState → Word → List E → Option E)
    (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  value : match bev s (s.getReg .x11) (eListAt s (s.getReg .x12) (s.getReg .x13).toNat) with
    | some v => t.getMem (s.getReg .x10) = 0 ∧ eAt t (s.getReg .x10 + 8) = v
    | none => t.getMem (s.getReg .x10) ≠ 0
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨
    Within a (stackLo s bytecodeEvalStack) bytecodeEvalStack ∨ Within a Runtime.nextAddr 8 ∨
    Runtime.Fresh s t a

abbrev BytecodeEvalSpec (BcOk : MachineState → Nat → Word → Prop)
    (bev : MachineState → Word → List E → Option E) : Prop :=
  FunSpec Image.code 0x80010e24 (BytecodeEvalPre BcOk) (BytecodeEvalPost bev)

end Vbb

end Rv64Verifier.Bus
