import Rv64Verifier.Proofs.Bytecode.Basic
import Rv64Verifier.Proofs.Contracts
import Rv64Verifier.Model.Bytecode
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `Bytecode` in memory, and the contracts `Bytecode::evaluate` is proved against

`Bytecode` (`crates/verifier/src/bytecode.rs`) as the image lays it out: four `Vec`s, `blocks`
(24-byte `Block`s: `index`, `words_end`, `bytes_end`) at `+0`, `words` (16-byte `(u64, usize)`) at
`+24`, `positions` (`u16`) at `+48`, `bytes` (`u16`) at `+72`, then `len` at `+96` and
`fiat_shamir_iv` (32 bytes) at `+104`. `readBytecode s p` is the `Model.BytecodeRust` the memory of
`s` holds at `p`, a `usize` read as its `toNat`; `BytecodeMem` says where its parts lie, mapped and
aligned.

`evaluate` calls `eq_kernel` (`EqKernelSpec`, stated here as a hypothesis: its proof is not yet
written), `vec![ZERO; 2048]` (`FromElemSpec`, the statement of
`Proofs/Multilinear/Contracts.lean`, repeated) and `<E as Mul>::mul` (`Contracts.MulSpec`).
-/

namespace Rv64Verifier.Proofs.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts

/-! ## The representation -/

/-- `n` `Block`s from `p`. -/
def blocksAt (s : MachineState) (p : Word) (n : Nat) : List Model.BlockRust :=
  (List.range n).map fun i ↦
    ⟨(s.getMem (p + BitVec.ofNat 64 (24 * i))).toNat,
      (s.getMem (p + BitVec.ofNat 64 (24 * i) + 8)).toNat,
      (s.getMem (p + BitVec.ofNat 64 (24 * i) + 16)).toNat⟩

/-- `n` `(u64, usize)`s from `p`. -/
def wordsAt (s : MachineState) (p : Word) (n : Nat) : List (BitVec 64 × Nat) :=
  (List.range n).map fun i ↦
    (s.getMem (p + BitVec.ofNat 64 (16 * i)), (s.getMem (p + BitVec.ofNat 64 (16 * i) + 8)).toNat)

/-- `n` `u16`s from `p`. -/
def halvesAt (s : MachineState) (p : Word) (n : Nat) : List (BitVec 16) :=
  (List.range n).map fun i ↦ s.getHalfword (p + BitVec.ofNat 64 (2 * i))

/-- The `Bytecode` at `p`. -/
def readBytecode (s : MachineState) (p : Word) : Model.BytecodeRust where
  len := (s.getMem (p + 96)).toNat
  fiatShamirIv := bytesAt s (p + 104) 32
  blocks := blocksAt s (vecPtr s p) (vecLen s p).toNat
  words := wordsAt s (vecPtr s (p + 24)) (vecLen s (p + 24)).toNat
  positions := halvesAt s (vecPtr s (p + 48)) (vecLen s (p + 48)).toNat
  bytes := halvesAt s (vecPtr s (p + 72)) (vecLen s (p + 72)).toNat

/-- The `Bytecode` at `p` and its four buffers are mapped and aligned. -/
structure BytecodeMem (s : MachineState) (p : Word) : Prop where
  self : Mapped p 136
  align : p.toNat % 8 = 0
  blocks : Mapped (vecPtr s p) (24 * (vecLen s p).toNat)
  blocksAlign : (vecPtr s p).toNat % 8 = 0
  words : Mapped (vecPtr s (p + 24)) (16 * (vecLen s (p + 24)).toNat)
  wordsAlign : (vecPtr s (p + 24)).toNat % 8 = 0
  positions : Mapped (vecPtr s (p + 48)) (2 * (vecLen s (p + 48)).toNat)
  positionsAlign : (vecPtr s (p + 48)).toNat % 2 = 0
  bytes : Mapped (vecPtr s (p + 72)) (2 * (vecLen s (p + 72)).toNat)
  bytesAlign : (vecPtr s (p + 72)).toNat % 2 = 0

/-- The `n` bytes from `a` miss the free heap and `NEXT`, the `m` bytes below `sp` and the 32
bytes from `out`: a function that writes only those leaves them. -/
@[rv_addr] def Clear (s : MachineState) (a : Word) (n : Nat) (m : Nat) (out : Word) : Prop :=
  Outside s a n ∧ Apart a n (stackLo s m) m ∧ Apart a n out 32

/-- Every part of the `Bytecode` at `p` is `Clear`. -/
structure BytecodeClear (s : MachineState) (p : Word) (m : Nat) (out : Word) : Prop where
  self : Clear s p 136 m out
  blocks : Clear s (vecPtr s p) (24 * (vecLen s p).toNat) m out
  words : Clear s (vecPtr s (p + 24)) (16 * (vecLen s (p + 24)).toNat) m out
  positions : Clear s (vecPtr s (p + 48)) (2 * (vecLen s (p + 48)).toNat) m out
  bytes : Clear s (vecPtr s (p + 72)) (2 * (vecLen s (p + 72)).toNat) m out

/-! ## `eq_kernel`, at `0x8000cb38` -/

/-- `eq_kernel`'s 208-byte frame and `mul`'s stack below it (`from_elem`'s and `Scaler::new`'s
are smaller). -/
@[rv_addr] def eqKernelStack : Nat := 208 + mulStack

/-- `a0` = where the `Vec` goes, `a1`/`a2` = the point, shorter than 64: the result and the point
apart from the free heap, the stack and each other; `.rodata` in place. -/
structure EqKernelPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  point : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  short : (s.getReg .x12).toNat < 64
  stack : RtStack s eqKernelStack
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s eqKernelStack) eqKernelStack
  pointFree : Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  pointStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s eqKernelStack)
    eqKernelStack
  pointOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  rodata : RodataOk s

/-- A new `Vec` of `eqKernelRust` of the point, `2^len` elements, its buffer freshly allocated;
memory changes only in the `Vec`, the stack, `NEXT` and the new allocation. -/
structure EqKernelPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 24 8
  len : (vecLen t (s.getReg .x10)).toNat = 2 ^ (s.getReg .x12).toNat
  elems : vecEs t (s.getReg .x10) = Model.eqKernelRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat)
  fresh : NewBuf s t (vecPtr t (s.getReg .x10)) (24 * 2 ^ (s.getReg .x12).toNat) 8
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s eqKernelStack) eqKernelStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev EqKernelSpec : Prop := FunSpec Image.code 0x8000cb38 EqKernelPre EqKernelPost

/-! ## `<E as SpecFromElem>::from_elem` (`vec![x; n]`), at `0x80005360`

As `Proofs/Multilinear/Contracts.lean` states it. -/

/-- `from_elem`'s 64-byte frame and `try_allocate_in`'s stack below it. -/
abbrev fromElemStack : Nat := MultilinearContracts.fromElemStack
abbrev FromElemPre := MultilinearContracts.FromElemPre
abbrev FromElemPost := MultilinearContracts.FromElemPost
abbrev FromElemSpec : Prop := MultilinearContracts.FromElemSpec

/-! ## `Bytecode::evaluate`, at `0x80010e24` -/

/-- `evaluate`'s 1968-byte frame and `eq_kernel`'s stack below it (`mul`'s and `from_elem`'s are
smaller). -/
@[rv_addr] def evalStack : Nat := 1968 + eqKernelStack

/-- `a0` = where the `Result<E, VerifierError>` goes (32 bytes), `a1` = the `Bytecode`, `a2`/`a3` =
the point: the result slot mapped, aligned, apart from the free heap and the stack; the `Bytecode`
mapped and its parts `Clear`; the point valid and `Clear`; the heap in shape, the stack above it,
`.rodata` in place. -/
structure EvaluatePre (s : MachineState) : Prop where
  heap : HeapOk s
  out : ValidMemRange (s.getReg .x10) 4
  outFree : Outside s (s.getReg .x10) 32
  outStack : Apart (s.getReg .x10) 32 (stackLo s evalStack) evalStack
  bc : BytecodeMem s (s.getReg .x11)
  bcClear : BytecodeClear s (s.getReg .x11) evalStack (s.getReg .x10)
  point : ValidMemRange (s.getReg .x12) (3 * (s.getReg .x13).toNat)
  pointClear : Clear s (s.getReg .x12) (24 * (s.getReg .x13).toNat) evalStack (s.getReg .x10)
  stack : RtStack s evalStack
  rodata : RodataOk s

/-- What `evaluate` may write: the result, the stack, `NEXT` and what it allocates. -/
@[rv_addr] def EvaluateW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 32 ∨ Within a (stackLo s evalStack) evalStack ∨ Within a nextAddr 8 ∨
    Fresh s t a

/-- `Ok` (tag `0`) with `evaluateRust`'s value, or `Err` (tag `1`) exactly when `evaluateRust`
fails; bytes, and doublewords none of whose bytes, `evaluate` may write keep their values. -/
structure EvaluatePost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  result : (t.getMem (s.getReg .x10) = 0 ∧
      Model.evaluateRust (readBytecode s (s.getReg .x11)) (eListAt s (s.getReg .x12) (s.getReg .x13).toNat) =
        some (eAt t (s.getReg .x10 + 8))) ∨
    (t.getMem (s.getReg .x10) = 1 ∧
      Model.evaluateRust (readBytecode s (s.getReg .x11)) (eListAt s (s.getReg .x12) (s.getReg .x13).toNat) =
        none)
  bytes : ∀ a, ¬ EvaluateW s t a → byteAt t a = byteAt s a
  frame : ∀ a, (∀ i < 8, ¬ EvaluateW s t (a + BitVec.ofNat 64 i)) → t.getMem a = s.getMem a

abbrev EvaluateSpec : Prop := FunSpec Image.code 0x80010e24 EvaluatePre EvaluatePost

end Rv64Verifier.Proofs.Bytecode
