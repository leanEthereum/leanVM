import Rv64Verifier.Proofs.Layout.Contracts
import Rv64Verifier.Proofs.Layout.ReprVec

/-!
# Contracts of the functions on `Vec<Form>` and `Flushes`

As `Contracts.lean`. A function that builds a `Vec<Form>` allocates every buffer it reaches
(`NewFormVec`); one that grows a `Vec` or `Flushes` in place says which of its bytes it writes and
that its new buffers are fresh. A caller keeps what it holds apart from those bytes, which the
values' `Ok`s make easy: everything a sound value reaches lies in the heap below `NEXT`
(`FormVecOk.deep_below`, ..), so whatever is allocated later is apart from it.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- What every constructor of a `Vec<Form>` at `out` ensures: a sound value, every buffer it reaches
allocated by the call, and memory changed only at `out`, the `n` bytes below `sp`, `NEXT` and what
it allocates. -/
structure NewFormVec (s t : MachineState) (out : Word) (n : Nat) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : FormVecOk t out
  fresh : ∀ x, formVecDeep t out x → Fresh s t x
  frame : DFrame s t fun a ↦ Within a out 24 ∨ Within a (stackLo s n) n ∨ Within a nextAddr 8 ∨
    Fresh s t a

/-! ## `Vec<Form>::spec_extend` from a slice, at `0x80011db8` -/

/-- Its 112-byte frame and the deepest of `reserve`'s, `try_allocate_in`'s and `memcpy`'s stacks. -/
@[rv_addr] def specExtendStack : Nat := 112 + reserveStack

/-- `a0` = the `Vec<Form>`; `a1`..`a2` = the slice of forms cloned onto it. The slice and the
forms' buffers miss what the call writes: the `Vec`'s header and buffer. -/
structure SpecExtendPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s specExtendStack
  self : ValidMemRange (s.getReg .x10) 3
  ok : FormVecOk s (s.getReg .x10)
  bounds : (s.getReg .x11).toNat ≤ (s.getReg .x12).toNat
  whole : ((s.getReg .x12).toNat - (s.getReg .x11).toNat) % 24 = 0
  src : ValidMemRange (s.getReg .x11) (((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 8)
  srcOk : FormsOk s (s.getReg .x11) (((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 24)
  selfFree : Outside s (s.getReg .x10) 24
  srcFree : Outside s (s.getReg .x11) ((s.getReg .x12).toNat - (s.getReg .x11).toNat)
  selfStack : Apart (s.getReg .x10) 24 (stackLo s specExtendStack) specExtendStack
  srcStack : Apart (s.getReg .x11) ((s.getReg .x12).toNat - (s.getReg .x11).toNat)
    (stackLo s specExtendStack) specExtendStack
  apart : ∀ x, (Within x (s.getReg .x11) ((s.getReg .x12).toNat - (s.getReg .x11).toNat) ∨
    formsDeep s (s.getReg .x11) (((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 24) x) →
      ¬ (Within x (s.getReg .x10) 24 ∨ formVecBuf s (s.getReg .x10) x)
  header : ∀ x, Within x (s.getReg .x10) 24 → ¬ formVecDeep s (s.getReg .x10) x

/-- The slice's forms cloned onto the end; new buffers fresh; memory changed only in the header,
the old buffer, the stack, `NEXT` and what it allocates. -/
structure SpecExtendPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : formVecOf t (s.getReg .x10) = formVecOf s (s.getReg .x10) ++
    formsAt s (s.getReg .x11) (((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 24)
  ok : FormVecOk t (s.getReg .x10)
  deep : ∀ x, formVecDeep t (s.getReg .x10) x → formVecDeep s (s.getReg .x10) x ∨ Fresh s t x
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨ formVecBuf s (s.getReg .x10) a ∨
    Within a (stackLo s specExtendStack) specExtendStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def SpecExtendSpec : Prop := FunSpec Image.code 0x80011db8 SpecExtendPre SpecExtendPost

/-! ## `<[&[Form]; 3]>::concat`, at `0x80011cb0` -/

@[rv_addr] def concatStack : Nat := 80 + specExtendStack

/-- The `i`-th of the three slices at `a`: its pointer at `a + 16 i`, its length at `a + 16 i + 8`. -/
def slicePtr (s : MachineState) (a : Word) (i : Nat) : Word := s.getMem (a + BitVec.ofNat 64 (16 * i))
def sliceLen (s : MachineState) (a : Word) (i : Nat) : Nat :=
  (s.getMem (a + BitVec.ofNat 64 (16 * i + 8))).toNat

/-- `a0` = where the `Vec<Form>` goes, `a1` = the three slices. -/
structure ConcatPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s concatStack
  out : ValidMemRange (s.getReg .x10) 3
  slices : ValidMemRange (s.getReg .x11) 6
  outFree : Outside s (s.getReg .x10) 24
  slicesFree : Outside s (s.getReg .x11) 48
  outStack : Apart (s.getReg .x10) 24 (stackLo s concatStack) concatStack
  slicesStack : Apart (s.getReg .x11) 48 (stackLo s concatStack) concatStack
  src : ∀ i < 3, ValidMemRange (slicePtr s (s.getReg .x11) i) (3 * sliceLen s (s.getReg .x11) i)
  srcOk : ∀ i < 3, FormsOk s (slicePtr s (s.getReg .x11) i) (sliceLen s (s.getReg .x11) i)
  srcFree : ∀ i < 3, Outside s (slicePtr s (s.getReg .x11) i) (24 * sliceLen s (s.getReg .x11) i)
  srcStack : ∀ i < 3, Apart (slicePtr s (s.getReg .x11) i) (24 * sliceLen s (s.getReg .x11) i)
    (stackLo s concatStack) concatStack

/-- The three slices' forms, cloned into a new `Vec`. -/
def ConcatSpec : Prop := FunSpec Image.code 0x80011cb0 ConcatPre fun s t ↦
  NewFormVec s t (s.getReg .x10) concatStack ∧
    formVecOf t (s.getReg .x10) =
      formsAt s (slicePtr s (s.getReg .x11) 0) (sliceLen s (s.getReg .x11) 0) ++
      formsAt s (slicePtr s (s.getReg .x11) 1) (sliceLen s (s.getReg .x11) 1) ++
      formsAt s (slicePtr s (s.getReg .x11) 2) (sliceLen s (s.getReg .x11) 2)

/-! ## `<Vec<Form> as Clone>::clone`, at `0x80006104` -/

@[rv_addr] def cloneStack : Nat := 128 + tryAllocStack

/-- `a0` = where the `Vec<Form>` goes, `a1`/`a2` = the slice cloned. -/
structure ClonePre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s cloneStack
  out : ValidMemRange (s.getReg .x10) 3
  src : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  srcOk : FormsOk s (s.getReg .x11) (s.getReg .x12).toNat
  outFree : Outside s (s.getReg .x10) 24
  srcFree : Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  outStack : Apart (s.getReg .x10) 24 (stackLo s cloneStack) cloneStack
  srcStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s cloneStack) cloneStack

def CloneSpec : Prop := FunSpec Image.code 0x80006104 ClonePre fun s t ↦
  NewFormVec s t (s.getReg .x10) cloneStack ∧
    formVecOf t (s.getReg .x10) = formsAt s (s.getReg .x11) (s.getReg .x12).toNat

/-! ## `Flushes::pair`, at `0x80011b98` -/

@[rv_addr] def pairStack : Nat := 48 + growOneStack

/-- `a0` = `self`; `a1`, `a2` = the `Vec<Form>`s pushed onto `push` and `pull` (moved: their
headers are copied). What the call writes, `self`'s header and buffers, misses the arguments. -/
structure PairPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s pairStack
  self : ValidMemRange (s.getReg .x10) 6
  ok : FlushesOk s (s.getReg .x10)
  push : ValidMemRange (s.getReg .x11) 3
  pull : ValidMemRange (s.getReg .x12) 3
  pushOk : FormVecOk s (s.getReg .x11)
  pullOk : FormVecOk s (s.getReg .x12)
  selfFree : Outside s (s.getReg .x10) 48
  pushFree : Outside s (s.getReg .x11) 24
  pullFree : Outside s (s.getReg .x12) 24
  selfStack : Apart (s.getReg .x10) 48 (stackLo s pairStack) pairStack
  pushStack : Apart (s.getReg .x11) 24 (stackLo s pairStack) pairStack
  pullStack : Apart (s.getReg .x12) 24 (stackLo s pairStack) pairStack
  apart : ∀ x, (Within x (s.getReg .x11) 24 ∨ formVecDeep s (s.getReg .x11) x ∨
    Within x (s.getReg .x12) 24 ∨ formVecDeep s (s.getReg .x12) x) →
      ¬ (Within x (s.getReg .x10) 48 ∨ flushesBuf s (s.getReg .x10) x)

/-- The two pushed; new buffers fresh; memory changed only in the header, the buffers, the stack,
`NEXT` and what it allocates. -/
structure PairPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : flushesOf t (s.getReg .x10) =
    (flushesOf s (s.getReg .x10)).pair (formVecOf s (s.getReg .x11)) (formVecOf s (s.getReg .x12))
  ok : FlushesOk t (s.getReg .x10)
  deep : ∀ x, flushesDeep t (s.getReg .x10) x → flushesDeep s (s.getReg .x10) x ∨
    formVecDeep s (s.getReg .x11) x ∨ formVecDeep s (s.getReg .x12) x ∨ Fresh s t x
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 48 ∨ flushesBuf s (s.getReg .x10) a ∨
    Within a (stackLo s pairStack) pairStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def PairSpec : Prop := FunSpec Image.code 0x80011b98 PairPre PairPost

/-! ## Growing a `Flushes` -/

/-- What the functions that push onto a `Flushes` at `a` ensure, from `s` to `t`, `n` bytes of stack
below `sp`: a sound `Flushes` reaching only what it reached, the buffers `m` of the forms moved into
it, and fresh buffers; memory changed only in its header and buffers, the stack, `NEXT` and what it
allocates. -/
structure GrowFlushes (s t : MachineState) (a : Word) (n : Nat) (m : Word → Prop) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : FlushesOk t a
  deep : ∀ x, flushesDeep t a x → flushesDeep s a x ∨ m x ∨ Fresh s t x
  frame : DFrame s t fun x ↦ Within x a 48 ∨ flushesBuf s a x ∨ Within x (stackLo s n) n ∨
    Within x nextAddr 8 ∨ Fresh s t x

/-- What they need: a sound `Flushes` outside the free heap and the stack, and `.rodata` for `pow`. -/
structure FlushesPre (n : Nat) (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s n
  self : ValidMemRange (s.getReg .x10) 6
  ok : FlushesOk s (s.getReg .x10)
  selfFree : Outside s (s.getReg .x10) 48
  selfStack : Apart (s.getReg .x10) 48 (stackLo s n) n
  rodata : RodataOk s

/-! ## `Flushes::state_derived`, at `0x80005e38`, and `state_step`, at `0x80004a90`

Both compiled for the one `pc` and `fp` every table passes, columns `0` and `1`. -/

@[rv_addr] def stateDerivedStack : Nat := 112 + colStack

/-- `a0` = `self`; `a1`, `a2` = `npc`, `nfp` (moved). -/
structure StateDerivedPre (s : MachineState) : Prop extends FlushesPre stateDerivedStack s where
  npc : ValidMemRange (s.getReg .x11) 3
  nfp : ValidMemRange (s.getReg .x12) 3
  npcOk : FormOk s (s.getReg .x11)
  nfpOk : FormOk s (s.getReg .x12)
  npcFree : Outside s (s.getReg .x11) 24
  nfpFree : Outside s (s.getReg .x12) 24
  npcStack : Apart (s.getReg .x11) 24 (stackLo s stateDerivedStack) stateDerivedStack
  nfpStack : Apart (s.getReg .x12) 24 (stackLo s stateDerivedStack) stateDerivedStack
  apart : ∀ x, (Within x (s.getReg .x11) 24 ∨ formBuf s (s.getReg .x11) x ∨
    Within x (s.getReg .x12) 24 ∨ formBuf s (s.getReg .x12) x) →
      ¬ (Within x (s.getReg .x10) 48 ∨ flushesBuf s (s.getReg .x10) x)

def StateDerivedSpec : Prop := FunSpec Image.code 0x80005e38 StateDerivedPre fun s t ↦
  GrowFlushes s t (s.getReg .x10) stateDerivedStack
      (fun x ↦ formBuf s (s.getReg .x11) x ∨ formBuf s (s.getReg .x12) x) ∧
    flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).stateDerived 0 1
      (formOf s (s.getReg .x11)) (formOf s (s.getReg .x12))

@[rv_addr] def stateStepStack : Nat := 64 + stateDerivedStack

def StateStepSpec : Prop := FunSpec Image.code 0x80004a90 (FlushesPre stateStepStack) fun s t ↦
  GrowFlushes s t (s.getReg .x10) stateStepStack (fun _ ↦ False) ∧
    flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).stateStep 0 1

end Rv64Verifier.Layout
