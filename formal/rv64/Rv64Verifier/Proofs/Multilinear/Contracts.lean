import Rv64Verifier.Proofs.Contracts
import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Proofs.Transcript.Repr

/-!
# Contracts of the multilinear helpers

Statements only (`multilinear.rs`, `field.rs`'s `powers`): a caller takes these as hypotheses,
and `Proofs/Multilinear/*.lean` prove them from their callees' contracts. Each says the code
computes its mirror in `Model/Multilinear.lean` (hence the statement's value, through the mirror's
`_eq` theorem), how many bytes below `sp` it may use, its callees' included, and what else it may
write.
-/

namespace Rv64Verifier.MultilinearContracts
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts

/-! ## `dot`, at `0x80007f3c` -/

/-- `dot`'s 96-byte frame and `mul`'s stack below it. -/
@[rv_addr] def dotStack : Nat := 96 + mulStack

/-- `a0` = the return slot, `a1`/`a2` = `left`, `a3`/`a4` = `right`: valid, the slices apart
from the result and from the stack, `.rodata` in place apart from the result and the stack. -/
structure DotPre (s : MachineState) : Prop where
  ret : ValidMemRange (s.getReg .x10) 3
  left : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  right : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x14).toNat)
  stack : StackOk s dotStack
  retLeft : Apart (s.getReg .x10) 24 (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  retRight : Apart (s.getReg .x10) 24 (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  retStack : Apart (s.getReg .x10) 24 (stackLo s dotStack) dotStack
  leftStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s dotStack) dotStack
  rightStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s dotStack) dotStack
  rodata : RodataOk s
  retRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize
  stackRodata : Apart (stackLo s dotStack) dotStack rodataBase rodataSize

/-- The lengths agree, the result is `dotRust` of the slices, and memory changes only in the
result and the stack. -/
structure DotPost (s t : MachineState) : Prop where
  len : s.getReg .x12 = s.getReg .x14
  value : eAt t (s.getReg .x10) = Model.dotRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat)
    (eListAt s (s.getReg .x13) (s.getReg .x12).toNat)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (stackLo s dotStack) dotStack →
    t.getMem a = s.getMem a

abbrev DotSpec : Prop := FunSpec Image.code 0x80007f3c DotPre DotPost

/-! ## `poly_eval`, at `0x8000cef4` -/

/-- `poly_eval`'s 96-byte frame and `mul`'s stack below it. -/
@[rv_addr] def polyEvalStack : Nat := 96 + mulStack

/-- `a0` = the return slot, `a1`/`a2` = the coefficients, `a3` = the point (an `E` passed by
reference): valid, the result apart from the coefficients, the point and the stack, both inputs
apart from the stack, `.rodata` in place apart from the result and the stack. -/
structure PolyEvalPre (s : MachineState) : Prop where
  ret : ValidMemRange (s.getReg .x10) 3
  coeffs : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  point : ValidMemRange (s.getReg .x13) 3
  stack : StackOk s polyEvalStack
  retCoeffs : Apart (s.getReg .x10) 24 (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  retPoint : Apart (s.getReg .x10) 24 (s.getReg .x13) 24
  retStack : Apart (s.getReg .x10) 24 (stackLo s polyEvalStack) polyEvalStack
  coeffsStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s polyEvalStack)
    polyEvalStack
  pointStack : Apart (s.getReg .x13) 24 (stackLo s polyEvalStack) polyEvalStack
  rodata : RodataOk s
  retRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize
  stackRodata : Apart (stackLo s polyEvalStack) polyEvalStack rodataBase rodataSize

/-- The result is `polyEvalRust` of the coefficients at the point; memory changes only in the
result and the stack. -/
structure PolyEvalPost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) =
    Model.polyEvalRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat) (eAt s (s.getReg .x13))
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 →
    ¬ Within a (stackLo s polyEvalStack) polyEvalStack → t.getMem a = s.getMem a

abbrev PolyEvalSpec : Prop := FunSpec Image.code 0x8000cef4 PolyEvalPre PolyEvalPost

/-! ## `index_mle`, at `0x80010cd4` -/

/-- `index_mle`'s 160-byte frame and `mul`'s stack below it (`E::square` uses none). -/
@[rv_addr] def indexMleStack : Nat := 160 + mulStack

/-- `a0` = the return slot, `a1`/`a2` = the point: valid, apart from each other and the stack,
`.rodata` in place apart from the stack. -/
structure IndexMlePre (s : MachineState) : Prop where
  ret : ValidMemRange (s.getReg .x10) 3
  point : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  stack : StackOk s indexMleStack
  retPoint : Apart (s.getReg .x10) 24 (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  retStack : Apart (s.getReg .x10) 24 (stackLo s indexMleStack) indexMleStack
  pointStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s indexMleStack)
    indexMleStack
  rodata : RodataOk s
  stackRodata : Apart (stackLo s indexMleStack) indexMleStack rodataBase rodataSize

/-- The result is `indexMleRust` of the point; memory changes only in the result and the
stack. -/
structure IndexMlePost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) =
    Model.indexMleRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 →
    ¬ Within a (stackLo s indexMleStack) indexMleStack → t.getMem a = s.getMem a

abbrev IndexMleSpec : Prop := FunSpec Image.code 0x80010cd4 IndexMlePre IndexMlePost

/-! ## `<Vec<E> as Clone>::clone`, at `0x8000897c`: a slice to a new `Vec` -/

/-- `clone`'s 64-byte frame and `try_allocate_in`'s stack below it (`memcpy`'s is smaller). -/
@[rv_addr] def cloneStack : Nat := 64 + Runtime.tryAllocStack

/-- `a0` = where the `Vec` goes, `a1`/`a2` = the slice: the result apart from the free heap, the
slice mapped, aligned, apart from the free heap, the result and the stack. -/
structure ClonePre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  src : Runtime.Mapped (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  srcAlign : (s.getReg .x11).toNat % 8 = 0
  stack : Runtime.RtStack s cloneStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s cloneStack) cloneStack
  srcFree : Runtime.Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  srcOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  srcStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s cloneStack) cloneStack

/-- A new `Vec` of the slice's elements, its buffer freshly allocated; memory changes only in the
`Vec`, the stack, `NEXT` and the new allocation. -/
structure ClonePost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  vec : Runtime.VecOk t (s.getReg .x10) 24 8
  len : Runtime.vecLen t (s.getReg .x10) = s.getReg .x12
  elems : Runtime.vecEs t (s.getReg .x10) = eListAt s (s.getReg .x11) (s.getReg .x12).toNat
  fresh : Runtime.NewBuf s t (Runtime.vecPtr t (s.getReg .x10)) (24 * (s.getReg .x12).toNat) 8
  frame : Runtime.ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s cloneStack) cloneStack ∨ Within a Runtime.nextAddr 8 ∨ Runtime.Fresh s t a

abbrev CloneSpec : Prop := FunSpec Image.code 0x8000897c ClonePre ClonePost

/-! ## `selector_point`, at `0x8000e1bc` -/

/-- `selector_point`'s 64-byte frame and `try_allocate_in`'s stack below it. -/
@[rv_addr] def selectorStack : Nat := 64 + Runtime.tryAllocStack

/-- `a0` = where the `Vec` goes, `a1` = the selector, `a2` = the length. -/
structure SelectorPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  stack : Runtime.RtStack s selectorStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s selectorStack) selectorStack

/-- A new `Vec` of `selectorPointRust selector length`, its buffer freshly allocated; memory
changes only in the `Vec`, the stack, `NEXT` and the new allocation. -/
structure SelectorPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  vec : Runtime.VecOk t (s.getReg .x10) 24 8
  len : Runtime.vecLen t (s.getReg .x10) = s.getReg .x12
  elems : Runtime.vecEs t (s.getReg .x10) =
    Model.selectorPointRust (s.getReg .x11) (s.getReg .x12).toNat
  fresh : Runtime.NewBuf s t (Runtime.vecPtr t (s.getReg .x10)) (24 * (s.getReg .x12).toNat) 8
  frame : Runtime.ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s selectorStack) selectorStack ∨ Within a Runtime.nextAddr 8 ∨
      Runtime.Fresh s t a

abbrev SelectorSpec : Prop := FunSpec Image.code 0x8000e1bc SelectorPre SelectorPost

/-! ## `Placement::eq_above`, at `0x8000e12c` -/

/-- `eq_eval`'s stack, which `eq_above` tail-calls; `selector_point`'s, below `eq_above`'s
80-byte frame, is smaller. -/
@[rv_addr] def eqAboveStack : Nat := 112 + mulStack

/-- `a0` = the return slot, `a1` = `variables`, `a2` = `index`, `a3`/`a4` = the point: the
result and the point apart from the free heap and the stack, `.rodata` in place. -/
structure EqAbovePre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  ret : ValidMemRange (s.getReg .x10) 3
  point : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x14).toNat)
  stack : Runtime.RtStack s eqAboveStack
  retFree : Runtime.Outside s (s.getReg .x10) 24
  pointFree : Runtime.Outside s (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  retStack : Apart (s.getReg .x10) 24 (stackLo s eqAboveStack) eqAboveStack
  pointStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s eqAboveStack)
    eqAboveStack
  rodata : RodataOk s

/-- What `eq_above` may write: the result, the stack, `NEXT` and what it allocates. -/
@[rv_addr] def EqAboveW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s eqAboveStack) eqAboveStack ∨
    Within a Runtime.nextAddr 8 ∨ Runtime.Fresh s t a

/-- The result is `PlacementRust.eqAbove` of the point; a doubleword none of whose bytes it may
write keeps its value. -/
structure EqAbovePost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  value : eAt t (s.getReg .x10) =
    Model.PlacementRust.eqAbove ⟨(s.getReg .x11).toNat, s.getReg .x12⟩
      (eListAt s (s.getReg .x13) (s.getReg .x14).toNat)
  frame : ∀ a, (∀ i < 8, ¬ EqAboveW s t (a + BitVec.ofNat 64 i)) → t.getMem a = s.getMem a

abbrev EqAboveSpec : Prop := FunSpec Image.code 0x8000e12c EqAbovePre EqAbovePost

/-! ## `<E as SpecFromElem>::from_elem` (`vec![x; n]`), at `0x80005360` -/

/-- `from_elem`'s 64-byte frame and `try_allocate_in`'s stack below it. -/
@[rv_addr] def fromElemStack : Nat := 64 + Runtime.tryAllocStack

/-- `a0` = where the `Vec` goes, `a1` = the element (an `E` by reference), `a2` = `n`: the result
and the element apart from the free heap, the stack and each other. -/
structure FromElemPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  elem : ValidMemRange (s.getReg .x11) 3
  stack : Runtime.RtStack s fromElemStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s fromElemStack) fromElemStack
  elemFree : Runtime.Outside s (s.getReg .x11) 24
  elemStack : Apart (s.getReg .x11) 24 (stackLo s fromElemStack) fromElemStack
  elemOut : Apart (s.getReg .x11) 24 (s.getReg .x10) 24

/-- A new `Vec` of `n` copies of the element, its buffer freshly allocated; memory changes only
in the `Vec`, the stack, `NEXT` and the new allocation. -/
structure FromElemPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  vec : Runtime.VecOk t (s.getReg .x10) 24 8
  len : Runtime.vecLen t (s.getReg .x10) = s.getReg .x12
  elems : Runtime.vecEs t (s.getReg .x10) =
    List.replicate (s.getReg .x12).toNat (eAt s (s.getReg .x11))
  fresh : Runtime.NewBuf s t (Runtime.vecPtr t (s.getReg .x10)) (24 * (s.getReg .x12).toNat) 8
  frame : Runtime.ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s fromElemStack) fromElemStack ∨ Within a Runtime.nextAddr 8 ∨
      Runtime.Fresh s t a

abbrev FromElemSpec : Prop := FunSpec Image.code 0x80005360 FromElemPre FromElemPost

/-! ## `powers`, at `0x80007dfc` -/

/-- `powers`' 144-byte frame and `mul`'s stack below it (`try_allocate_in`'s is smaller). -/
@[rv_addr] def powersStack : Nat := 144 + mulStack

/-- `a0` = where the `Vec` goes, `a1` = the base (an `E` by reference), `a2` = `count`: the result
and the base apart from the free heap, the stack, `.rodata` and each other; `.rodata` in place. -/
structure PowersPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  base : ValidMemRange (s.getReg .x11) 3
  stack : Runtime.RtStack s powersStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s powersStack) powersStack
  outRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize
  baseFree : Runtime.Outside s (s.getReg .x11) 24
  baseStack : Apart (s.getReg .x11) 24 (stackLo s powersStack) powersStack
  baseOut : Apart (s.getReg .x11) 24 (s.getReg .x10) 24
  rodata : RodataOk s

/-- What `powers` may write: the result, the stack, `NEXT` and what it allocates. -/
@[rv_addr] def PowersW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s powersStack) powersStack ∨
    Within a Runtime.nextAddr 8 ∨ Runtime.Fresh s t a

/-- A new `Vec` of `powers base count`, its buffer freshly allocated; a doubleword none of whose
bytes it may write keeps its value (`mul`'s contract frames doublewords, not bytes). -/
structure PowersPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  vec : Runtime.VecOk t (s.getReg .x10) 24 8
  len : Runtime.vecLen t (s.getReg .x10) = s.getReg .x12
  elems : Runtime.vecEs t (s.getReg .x10) =
    LeanVM.Protocol.Verifier.powers (eAt s (s.getReg .x11)) (s.getReg .x12).toNat
  fresh : Runtime.NewBuf s t (Runtime.vecPtr t (s.getReg .x10)) (24 * (s.getReg .x12).toNat) 8
  frame : ∀ a, (∀ i < 8, ¬ PowersW s t (a + BitVec.ofNat 64 i)) → t.getMem a = s.getMem a

abbrev PowersSpec : Prop := FunSpec Image.code 0x80007dfc PowersPre PowersPost

/-! ## `Scaler::new`, at `0x80008a58` -/

/-- `Scaler::new`'s 112-byte frame and `from_elem`'s stack below it. -/
@[rv_addr] def scalerStack : Nat := 112 + fromElemStack

/-- `a0` = the result (a tag and a `Vec` or an `E`, 32 bytes), `a1` = `r` (by reference),
`a2` = `uses`. -/
structure ScalerPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : ValidMemRange (s.getReg .x10) 4
  r : ValidMemRange (s.getReg .x11) 3
  stack : Runtime.RtStack s scalerStack
  outFree : Runtime.Outside s (s.getReg .x10) 32
  outStack : Apart (s.getReg .x10) 32 (stackLo s scalerStack) scalerStack
  rFree : Runtime.Outside s (s.getReg .x11) 24
  rStack : Apart (s.getReg .x11) 24 (stackLo s scalerStack) scalerStack
  rOut : Apart (s.getReg .x11) 24 (s.getReg .x10) 32
  rodata : RodataOk s

/-- Under `256` uses `Plain(r)` (tag `1`); from `256` on `Table`, the `Vec` of `Scaled::new(r)`
(tag `0`), its buffer freshly allocated. -/
structure ScalerPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  plain : (s.getReg .x12).toNat < 256 →
    t.getMem (s.getReg .x10) = 1 ∧ eAt t (s.getReg .x10 + 8) = eAt s (s.getReg .x11)
  table : 256 ≤ (s.getReg .x12).toNat → t.getMem (s.getReg .x10) = 0 ∧
    Runtime.VecOk t (s.getReg .x10 + 8) 24 8 ∧ Runtime.vecLen t (s.getReg .x10 + 8) = 2112 ∧
    (Runtime.vecEs t (s.getReg .x10 + 8)).map Model.limbs =
      Model.scaledTable (Model.limbs (eAt s (s.getReg .x11))) ∧
    Runtime.NewBuf s t (Runtime.vecPtr t (s.getReg .x10 + 8)) (24 * 2112) 8
  frame : Runtime.ByteFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨
    Within a (stackLo s scalerStack) scalerStack ∨ Within a Runtime.nextAddr 8 ∨
      Runtime.Fresh s t a

abbrev ScalerSpec : Prop := FunSpec Image.code 0x80008a58 ScalerPre ScalerPost

/-! ## `<Vec<E> as SpecExtend<&E, slice::Iter<E>>>::spec_extend`, at `0x8000e520`, with room
enough -/

/-- `spec_extend`'s 48-byte frame and `memcpy`'s stack below it. -/
@[rv_addr] def extendStack : Nat := 48 + Runtime.memcpyStack

/-- The slice's length, `(a2 - a1) / 24`. -/
def extendLen (s : MachineState) : Nat := ((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 24

/-- Where the new elements go: past the `Vec`'s length. -/
def extendDst (s : MachineState) : Word :=
  Runtime.vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (24 * (Runtime.vecLen s (s.getReg .x10)).toNat)

/-- `a0` = the `Vec` (with room for the slice), `a1`..`a2` = the slice: aligned, mapped unless
empty, the slice, the `Vec` and its free capacity apart from each other and from the stack. -/
structure ExtendPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  vec : ValidMemRange (s.getReg .x10) 3
  ok : Runtime.VecOk s (s.getReg .x10) 24 8
  room : (Runtime.vecLen s (s.getReg .x10)).toNat + extendLen s ≤
    (Runtime.vecCap s (s.getReg .x10)).toNat
  bounds : (s.getReg .x11).toNat ≤ (s.getReg .x12).toNat
  whole : ((s.getReg .x12).toNat - (s.getReg .x11).toNat) % 24 = 0
  src : extendLen s = 0 ∨ Runtime.Mapped (s.getReg .x11) (24 * extendLen s)
  srcAlign : extendLen s = 0 ∨ (s.getReg .x11).toNat % 8 = 0
  stack : Runtime.RtStack s extendStack
  vecStack : Apart (s.getReg .x10) 24 (stackLo s extendStack) extendStack
  vecHeap : Runtime.Outside s (s.getReg .x10) 24
  srcStack : Apart (s.getReg .x11) (24 * extendLen s) (stackLo s extendStack) extendStack
  srcVec : Apart (s.getReg .x11) (24 * extendLen s) (s.getReg .x10) 24
  srcDst : Apart (s.getReg .x11) (24 * extendLen s) (extendDst s) (24 * extendLen s)
  dstVec : Apart (extendDst s) (24 * extendLen s) (s.getReg .x10) 24

/-- The slice's elements appended: the length grown, the capacity and buffer kept, the new
elements the slice's; memory changes only in the length, the new elements and the stack. -/
structure ExtendPost (s t : MachineState) : Prop where
  len : (Runtime.vecLen t (s.getReg .x10)).toNat =
    (Runtime.vecLen s (s.getReg .x10)).toNat + extendLen s
  cap : Runtime.vecCap t (s.getReg .x10) = Runtime.vecCap s (s.getReg .x10)
  ptr : Runtime.vecPtr t (s.getReg .x10) = Runtime.vecPtr s (s.getReg .x10)
  new : eListAt t (extendDst s) (extendLen s) = eListAt s (s.getReg .x11) (extendLen s)
  next : Runtime.heapNext t = Runtime.heapNext s
  frame : Runtime.ByteFrame s t fun a ↦ Within a (s.getReg .x10 + 16) 8 ∨
    Within a (extendDst s) (24 * extendLen s) ∨ Within a (stackLo s extendStack) extendStack

abbrev ExtendSpec : Prop := FunSpec Image.code 0x8000e520 ExtendPre ExtendPost

/-! ## `eq_kernel`, at `0x8000cb38`

Stated as `Proofs/Gkr/Contracts.lean` states it, field for field. -/

/-- `eq_kernel`'s 208-byte frame and `mul`'s stack below it (`Scaler::new`'s and `from_elem`'s are
smaller). -/
@[rv_addr] def eqKernelStack : Nat := 208 + mulStack

/-- `a0` = where the `Vec` goes, `a1`/`a2` = the point (its pointer arbitrary when empty). -/
structure EqKernelPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : Transcript.Region (s.getReg .x10) 24
  point : (s.getReg .x12).toNat = 0 ∨ Transcript.Region (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  stack : Runtime.RtStack s eqKernelStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  pointFree : (s.getReg .x12).toNat = 0 ∨
    Runtime.Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  outStack : Apart (s.getReg .x10) 24 (stackLo s eqKernelStack) eqKernelStack
  pointStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s eqKernelStack)
    eqKernelStack
  pointOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize

/-- A new `Vec` of `eqKernelRust` of the point; memory changes only in the `Vec`, the stack,
`NEXT` and the new allocation. -/
structure EqKernelPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  value : Transcript.NewVecE s t (s.getReg .x10)
    (Model.eqKernelRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat))
  frame : Transcript.DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s eqKernelStack) eqKernelStack ∨ Within a Runtime.nextAddr 8 ∨
      Runtime.Fresh s t a

abbrev EqKernelSpec : Prop := FunSpec Image.code 0x8000cb38 EqKernelPre EqKernelPost

/-! ## `multilinear_eval::<E>`, at `0x8000d28c` -/

/-- `multilinear_eval`'s 208-byte frame and `mul`'s stack below it (`Scaler::new`'s,
`try_allocate_in`'s and `memcpy`'s are smaller). -/
@[rv_addr] def mleEvalStack : Nat := 208 + mulStack

/-- `a0` = the `Result<E, VerifierError>` (32 bytes), `a1`/`a2` = the table, `a3`/`a4` = the
point, either slice's pointer arbitrary when empty. -/
structure MleEvalPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : Transcript.Region (s.getReg .x10) 32
  mle : (s.getReg .x12).toNat = 0 ∨ Transcript.Region (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  point : (s.getReg .x14).toNat = 0 ∨
    Transcript.Region (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  stack : Runtime.RtStack s mleEvalStack
  outFree : Runtime.Outside s (s.getReg .x10) 32
  mleFree : (s.getReg .x12).toNat = 0 ∨
    Runtime.Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  pointFree : (s.getReg .x14).toNat = 0 ∨
    Runtime.Outside s (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  outStack : Apart (s.getReg .x10) 32 (stackLo s mleEvalStack) mleEvalStack
  mleStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s mleEvalStack)
    mleEvalStack
  pointStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s mleEvalStack)
    mleEvalStack
  mleOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 32
  pointOut : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (s.getReg .x10) 32
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) 32 rodataBase rodataSize

/-- `Ok(multilinearEvalRust mle point)` (tag `0`, the value at `a0 + 8`) when the sizes match,
`Err` (tag `1`) otherwise; memory changes only in the result, the stack, `NEXT` and what it
allocates. -/
structure MleEvalPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  value : match Model.multilinearEvalRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat)
      (eListAt s (s.getReg .x13) (s.getReg .x14).toNat) with
    | some v => t.getMem (s.getReg .x10) = 0 ∧ eAt t (s.getReg .x10 + 8) = v
    | none => t.getMem (s.getReg .x10) = 1
  frame : Transcript.DFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨
    Within a (stackLo s mleEvalStack) mleEvalStack ∨ Within a Runtime.nextAddr 8 ∨
      Runtime.Fresh s t a

abbrev MleEvalSpec : Prop := FunSpec Image.code 0x8000d28c MleEvalPre MleEvalPost

/-! ## `<[&[E]] as Concat<E>>::concat`, at `0x8000cfc4` -/

/-- Its 64-byte frame and the deepest callee's stack below it, as `Proofs/Pcs/Contracts.lean`
bounds it. -/
@[rv_addr] def sliceConcatStack : Nat := 64 + Runtime.reserveStack

/-- The `i`-th slice's pointer and length. -/
@[rv_addr] def partPtr (s : MachineState) (i : Nat) : Word :=
  s.getMem (s.getReg .x11 + BitVec.ofNat 64 (16 * i))
@[rv_addr] def partLen (s : MachineState) (i : Nat) : Nat :=
  (s.getMem (s.getReg .x11 + BitVec.ofNat 64 (16 * i) + 8)).toNat

/-- The slices' elements, in order. -/
def parts (s : MachineState) : List (List E) :=
  (List.range (s.getReg .x12).toNat).map fun i ↦ eListAt s (partPtr s i) (partLen s i)

/-- `a0` = where the `Vec` goes, `a1`/`a2` = the slices (at least one: the compiled length loop
runs once before its test), each one's pointer arbitrary when empty. -/
structure SliceConcatPre (s : MachineState) : Prop where
  heap : Runtime.HeapOk s
  out : Transcript.Region (s.getReg .x10) 24
  count : 0 < (s.getReg .x12).toNat
  slices : Transcript.Region (s.getReg .x11) (16 * (s.getReg .x12).toNat)
  stack : Runtime.RtStack s sliceConcatStack
  outFree : Runtime.Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s sliceConcatStack) sliceConcatStack
  slicesFree : Runtime.Outside s (s.getReg .x11) (16 * (s.getReg .x12).toNat)
  slicesStack : Apart (s.getReg .x11) (16 * (s.getReg .x12).toNat) (stackLo s sliceConcatStack)
    sliceConcatStack
  slicesOut : Apart (s.getReg .x11) (16 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  part : ∀ i < (s.getReg .x12).toNat, partLen s i = 0 ∨
    (Transcript.Region (partPtr s i) (24 * partLen s i) ∧
      Runtime.Outside s (partPtr s i) (24 * partLen s i) ∧
      Apart (partPtr s i) (24 * partLen s i) (stackLo s sliceConcatStack) sliceConcatStack ∧
      Apart (partPtr s i) (24 * partLen s i) (s.getReg .x10) 24)

/-- A new `Vec` of the slices' elements, its pointer the dangling `8` when it has no capacity;
memory changes only in the `Vec`, the stack, `NEXT` and the new allocation. -/
structure SliceConcatPost (s t : MachineState) : Prop where
  heap : Runtime.HeapOk t
  mono : Runtime.heapNext s ≤ Runtime.heapNext t
  value : Transcript.NewVecE s t (s.getReg .x10) (parts s).flatten
  frame : Transcript.DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s sliceConcatStack) sliceConcatStack ∨ Within a Runtime.nextAddr 8 ∨
      Runtime.Fresh s t a
  dangling : Runtime.vecCap t (s.getReg .x10) = 0 → Runtime.vecPtr t (s.getReg .x10) = 8

abbrev SliceConcatSpec : Prop := FunSpec Image.code 0x8000cfc4 SliceConcatPre SliceConcatPost

end Rv64Verifier.MultilinearContracts
