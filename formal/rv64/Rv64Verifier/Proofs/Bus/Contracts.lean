import Rv64Verifier.Proofs.Bus.Repr
import Rv64Verifier.Proofs.Transcript.Contracts

/-!
# Contracts of the bus

`bus.rs`'s functions as compiled, each a `FunSpec`: when it returns, it computes its mirror
(`Model/Bus.lean`) on the values its arguments hold (`Repr.lean`); a panic is a trap, a dead end.
Each states the bytes below `sp` it may use, its callees' included (`*Stack`), and the memory it
may change.
-/

namespace Rv64Verifier.Bus
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.MultilinearContracts Rv64Verifier.Transcript

/-! ## `verify_bus_balance::{closure#2}`, the `fingerprints` closure, at `0x8001174c` -/

/-- The closure's 432-byte frame and `dot`'s stack below it (`alloc` uses none). -/
@[rv_addr] def fingerprintsStack : Nat := 432 + dotStack

/-- The captures, through the environment at `a1`: `&weights`, `&memory_index`, `&memory`,
`&bytecode_index`, `&bytecode_value`. -/
def capWeights (s : MachineState) : Word := s.getMem (s.getReg .x11)
def capMemoryIndex (s : MachineState) : Word := s.getMem (s.getReg .x11 + 8)
def capMemory (s : MachineState) : Word := s.getMem (s.getReg .x11 + 16)
def capBytecodeIndex (s : MachineState) : Word := s.getMem (s.getReg .x11 + 24)
def capBytecodeValue (s : MachineState) : Word := s.getMem (s.getReg .x11 + 32)

/-- `a0` = where the `Vec<E>` goes, `a1` = the environment, `a2`, `a3`, `a4` = `pc`,
`memory_count`, `bytecode_count` (each an `E` by reference). Everything read is `Held`; the result
lies outside the free heap and apart from the stack. -/
structure FingerprintsPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s fingerprintsStack
  rodata : RodataOk s
  out : ValidMemRange (s.getReg .x10) 3
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s fingerprintsStack) fingerprintsStack
  env : Held s fingerprintsStack (s.getReg .x11) 40
  weights : EVecHeld s fingerprintsStack (capWeights s)
  memory : EVecHeld s fingerprintsStack (capMemory s)
  memoryIndex : Held s fingerprintsStack (capMemoryIndex s) 24
  bytecodeIndex : Held s fingerprintsStack (capBytecodeIndex s) 24
  bytecodeValue : Held s fingerprintsStack (capBytecodeValue s) 24
  pc : Held s fingerprintsStack (s.getReg .x12) 24
  memoryCount : Held s fingerprintsStack (s.getReg .x13) 24
  bytecodeCount : Held s fingerprintsStack (s.getReg .x14) 24

/-- What the closure may write: the result, the stack, `NEXT` and what it allocates. -/
@[rv_addr] def FingerprintsW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s fingerprintsStack) fingerprintsStack ∨
    Within a nextAddr 8 ∨ Fresh s t a

/-- A new `Vec` of the three fingerprints (`weights` has at least six elements and `memory` three,
or the closure traps); a doubleword none of whose bytes it may write keeps its value. -/
structure FingerprintsPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 24 8
  cap : vecCap t (s.getReg .x10) = 3
  len : vecLen t (s.getReg .x10) = 3
  elems : vecEs t (s.getReg .x10) =
    fingerprintsRust (vecEs s (capWeights s)) (eAt s (capMemoryIndex s)) (vecEs s (capMemory s))
      (eAt s (capBytecodeIndex s)) (eAt s (capBytecodeValue s)) (eAt s (s.getReg .x12))
      (eAt s (s.getReg .x13)) (eAt s (s.getReg .x14))
  weightsLen : 6 ≤ (vecLen s (capWeights s)).toNat
  memoryLen : 3 ≤ (vecLen s (capMemory s)).toNat
  fresh : NewBuf s t (vecPtr t (s.getReg .x10)) 72 8
  frame : ∀ a, (∀ i < 8, ¬ FingerprintsW s t (a + BitVec.ofNat 64 i)) →
    t.getMem a = s.getMem a

abbrev FingerprintsSpec : Prop := FunSpec Image.code 0x8001174c FingerprintsPre FingerprintsPost

/-! ## Callees without a contract elsewhere -/

/-- `Form::evaluate`, at `0x80010924`: its 144-byte frame and `mul`'s stack below it. -/
@[rv_addr] def formEvaluateStack : Nat := 144 + Contracts.mulStack

/-- `a0` = the result, `a1`/`a2` = the form's terms (48 bytes each), `a3`/`a4` = the columns. -/
structure FormEvaluatePre (s : MachineState) : Prop where
  ret : Region (s.getReg .x10) 24
  terms : Region (s.getReg .x11) (48 * (s.getReg .x12).toNat)
  columns : Region (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  stack : RtStack s formEvaluateStack
  retStack : Apart (s.getReg .x10) 24 (stackLo s formEvaluateStack) formEvaluateStack
  termsStack : Apart (s.getReg .x11) (48 * (s.getReg .x12).toNat) (stackLo s formEvaluateStack)
    formEvaluateStack
  columnsStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s formEvaluateStack)
    formEvaluateStack
  rodata : RodataOk s
  retRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize

/-- The form's value at the row (a column out of range traps); memory changes only in the result
and the stack. -/
structure FormEvaluatePost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) =
    (LayoutMirror.FormRust.mk (termsAt s (s.getReg .x11) (s.getReg .x12).toNat)).evaluate
      (eListAt s (s.getReg .x13) (s.getReg .x14).toNat)
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s formEvaluateStack) formEvaluateStack

abbrev FormEvaluateSpec : Prop := FunSpec Image.code 0x80010924 FormEvaluatePre FormEvaluatePost

/-- `<Option<E> as SpecFromElem>::from_elem` (`vec![x; n]`), at `0x80010724`: its 80-byte frame
and `reserve`'s stack below it. -/
@[rv_addr] def optFromElemStack : Nat := 80 + reserveStack

/-- `a0` = where the `Vec` goes, `a1` = the element (an `Option<E>`, 32 bytes, by reference),
`a2` = `n`. -/
structure OptFromElemPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : Region (s.getReg .x10) 24
  elem : Region (s.getReg .x11) 32
  stack : RtStack s optFromElemStack
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s optFromElemStack) optFromElemStack
  elemFree : Outside s (s.getReg .x11) 32
  elemStack : Apart (s.getReg .x11) 32 (stackLo s optFromElemStack) optFromElemStack
  elemOut : Apart (s.getReg .x11) 32 (s.getReg .x10) 24

/-- A new `Vec` of `n` copies of the element, its buffer freshly allocated. -/
structure OptFromElemPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 32 8
  len : vecLen t (s.getReg .x10) = s.getReg .x12
  elems : optEListAt t (vecPtr t (s.getReg .x10)) (s.getReg .x12).toNat =
    List.replicate (s.getReg .x12).toNat (optEAt s (s.getReg .x11))
  fresh : NewBuf s t (vecPtr t (s.getReg .x10)) (32 * (s.getReg .x12).toNat) 8
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s optFromElemStack) optFromElemStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev OptFromElemSpec : Prop := FunSpec Image.code 0x80010724 OptFromElemPre OptFromElemPost

/-! ## `table_sumcheck`, at `0x80008010`

`fastcc`: `a0` = the `Result<Vec<TableEvaluations>, VerifierError>`, `a1`/`a2` = `tables` (80-byte
`Table`s, the opcode at `+72`), `a3`/`a4` = `table_log_heights`, `a5`/`a6` = `bus_forms`
(`Vec<Form>`s), `a7`/`t3` = `constraint_powers`, `t4`/`t5` = `form_powers`, `t6` and the stack's
`[sp]` = `equality_point`, `[sp + 8]` = `&target` (the callee owns it: `sumcheck` overwrites it),
`[sp + 16]` = the transcript. -/

/-- The 496-byte frame and `sumcheck`'s stack below it, the deepest of the callees'. -/
@[rv_addr] def tableSumcheckStack : Nat := 496 + sumcheckStack

def tsEqLen (s : MachineState) : Word := s.getMem (s.getReg .x2)
def tsTarget (s : MachineState) : Word := s.getMem (s.getReg .x2 + 8)
def tsSelf (s : MachineState) : Word := s.getMem (s.getReg .x2 + 16)

/-- The result and `target`: what the function writes besides the transcript and the stack. -/
def tsWrites (s : MachineState) : List (Word × Nat) := [(s.getReg .x10, 24), (tsTarget s, 24)]

/-- The statement's table of each `Table` from `a`: the one its opcode names (an opcode past the
list traps). -/
def tablesAt (s : MachineState) (a : Word) (n : Nat) : List Table :=
  (List.range n).map fun i ↦
    tables.getD (s.getMem (a + BitVec.ofNat 64 (80 * i + 72))).toNat default

/-- The `n` words from `a`, as numbers. -/
def natsAt (s : MachineState) (a : Word) (n : Nat) : List ℕ :=
  (s.readWords a n).map BitVec.toNat

/-- The `m` bytes from `a` are read only by a function that writes the `n` bytes below `sp`,
the regions `ws` and the transcript's sponge and offsets at `p`: valid, outside the free heap
and `NEXT`, apart from all of them. -/
structure RO (s : MachineState) (n : Nat) (ws : List (Word × Nat)) (p a : Word) (m : Nat) :
    Prop where
  region : m = 0 ∨ Region a m
  free : Outside s a m
  stack : Apart a m (stackLo s n) n
  out : ∀ x ∈ ws, Apart a m x.1 x.2
  self : Apart a m (p + 8) 344

/-- Every `Vec<Form>` from `a` (`n` of them), every form's header and every form's terms are
read only. -/
structure FormRowsRO (s : MachineState) (n : Nat) (ws : List (Word × Nat)) (p a : Word) (k : Nat) :
    Prop where
  rows : RO s n ws p a (24 * k)
  forms : ∀ i < k, RO s n ws p (vecPtr s (a + BitVec.ofNat 64 (24 * i)))
    (24 * (vecLen s (a + BitVec.ofNat 64 (24 * i))).toNat)
  terms : ∀ i < k, ∀ j < (vecLen s (a + BitVec.ofNat 64 (24 * i))).toNat,
    RO s n ws p (vecPtr s (vecPtr s (a + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j)))
      (48 * (vecLen s (vecPtr s (a + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j))).toNat)

structure TableSumcheckPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s tableSumcheckStack
  rodata : RodataOk s
  out : Region (s.getReg .x10) 24
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s tableSumcheckStack) tableSumcheckStack
  outRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize
  args : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x2) 24
  self : TranscriptOk s (tsSelf s)
  checked : byteAt s (tsSelf s + 360) ≠ 0
  selfStack : Apart (tsSelf s) transcriptSize (stackLo s tableSumcheckStack) tableSumcheckStack
  selfOut : Apart (tsSelf s) transcriptSize (s.getReg .x10) 24
  selfFree : Outside s (tsSelf s) transcriptSize
  selfRodata : Apart (tsSelf s) transcriptSize rodataBase rodataSize
  proofStack : ProofApart s (tsSelf s) (stackLo s tableSumcheckStack) tableSumcheckStack
  proofOut : ProofApart s (tsSelf s) (s.getReg .x10) 24
  proofFree : Outside s (proofAt s (tsSelf s)) 48
  streamFree : Outside s (streamPtr s (tsSelf s)) (24 * streamLen s (tsSelf s))
  target : Region (tsTarget s) 24
  targetFree : Outside s (tsTarget s) 24
  targetStack : Apart (tsTarget s) 24 (stackLo s tableSumcheckStack) tableSumcheckStack
  targetOut : Apart (tsTarget s) 24 (s.getReg .x10) 24
  targetSelf : Apart (tsTarget s) 24 (tsSelf s) transcriptSize
  proofTarget : ProofApart s (tsSelf s) (tsTarget s) 24
  targetRodata : Apart (tsTarget s) 24 rodataBase rodataSize
  tables : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x11)
    (80 * (s.getReg .x12).toNat)
  heights : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x13)
    (8 * (s.getReg .x14).toNat)
  forms : FormRowsRO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x15)
    (s.getReg .x16).toNat
  constraintPowers : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x17)
    (24 * (s.getReg .x28).toNat)
  formPowers : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x29)
    (24 * (s.getReg .x30).toNat)
  equalityPoint : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x31)
    (24 * (tsEqLen s).toNat)

/-- The `Vec<(Vec<E>, Vec<E>)>` at `a` holds `rows`: every buffer allocated from `s` on. -/
structure RowsAt (s t : MachineState) (a : Word) (rows : List (List E × List E)) : Prop where
  vec : VecOk t a 48 8
  fresh : NewBuf s t (vecPtr t a) (48 * (vecCap t a).toNat) 8
  len : (vecLen t a).toNat = rows.length
  pairs : ∀ i (h : i < rows.length),
    NewVecE s t (vecPtr t a + BitVec.ofNat 64 (48 * i)) rows[i].1 ∧
      NewVecE s t (vecPtr t a + BitVec.ofNat 64 (48 * i + 24)) rows[i].2

/-- `Ok(rows)` exactly when `tableSumcheckM` returns them, the transcript then standing for the
mirror's; otherwise `Err` (`errNiche` in the capacity). Memory changes only in the result,
`target`, the transcript's sponge and offsets, the stack, `NEXT` and the heap allocated. -/
structure TableSumcheckPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (tsSelf s) T →
    match (tableSumcheckM (tablesAt s (s.getReg .x11) (s.getReg .x12).toNat)
        (natsAt s (s.getReg .x13) (s.getReg .x14).toNat)
        (formRowsAt s (s.getReg .x15) (s.getReg .x16).toNat)
        (eListAt s (s.getReg .x17) (s.getReg .x28).toNat)
        (eListAt s (s.getReg .x29) (s.getReg .x30).toNat)
        (eListAt s (s.getReg .x31) (tsEqLen s).toNat) (eAt s (tsTarget s))).run T with
    | some (rows, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧
        RowsAt s t (s.getReg .x10) rows ∧ TranscriptAt t (tsSelf s) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨ Within a (tsTarget s) 24 ∨
    Within a (tsSelf s + 8) 344 ∨ Within a (stackLo s tableSumcheckStack) tableSumcheckStack ∨
    Within a nextAddr 8 ∨ Fresh s t a

abbrev TableSumcheckSpec : Prop :=
  FunSpec Image.code 0x80008010 TableSumcheckPre TableSumcheckPost

/-! ## `verify_bus_balance`, at `0x80006428`

`a0` = the `Result<BusResult, VerifierError>` (120 bytes), `a1` = the `Layout`, `a2` = the
transcript. Read off the code: a `Layout` holds `tables: Vec<Table>` at `+0`, `push`, `pull`,
`count` (`Vec<BusBlock>`) at `+24`, `+48`, `+72`, `&Bytecode` at `+144`, `log_memory` at `+152`,
`log_bytecode` at `+160`; a `BusBlock` (48 bytes) its `coordinates: Vec<Form>` at `+0`, `log_rows`
at `+24`, `rows` at `+32`, `owner` at `+40`; a `Table` (80 bytes) its `padding: Vec<E>` at `+0`;
a `BusResult` its `claims`, `bytecode_point`, `point`, `forms`, `totals` at `+0`, `+24`, `+48`,
`+72`, `+96`, the `Err` niche (`errNiche`) in `claims`' capacity; a `ColumnClaim` (56 bytes) its
`point: Vec<E>` at `+0`, `column` at `+24`, `value` at `+32`. -/

/-- The 1344-byte frame and `Bytecode::evaluate`'s stack below it, the deepest of the callees':
its 1968-byte frame and `eq_kernel`'s, 208 bytes and `mul`'s. -/
@[rv_addr] def busBalanceStack : Nat := 1344 + (1968 + (208 + Contracts.mulStack))

/-- The `BusBlock` at `a`. -/
def blockAt (s : MachineState) (a : Word) : BusBlock :=
  ⟨(s.getMem (a + 24)).toNat, (s.getMem (a + 32)).toNat, formVecAt s a,
    (s.getMem (a + 40)).toNat⟩

/-- The blocks of the `Vec<BusBlock>` at `a`. -/
def blocksAt (s : MachineState) (a : Word) : List BusBlock :=
  (List.range (vecLen s a).toNat).map fun i ↦ blockAt s (vecPtr s a + BitVec.ofNat 64 (48 * i))

/-- What `verify_bus_balance` reads of the `Layout` at `a`, as the statement's `Layout`; the fields
it does not read are left empty. -/
def busLayoutAt (s : MachineState) (a : Word) : Layout where
  logMemory := (s.getMem (a + 152)).toNat
  logBytecode := (s.getMem (a + 160)).toNat
  bytecode := []
  push := blocksAt s (a + 24)
  pull := blocksAt s (a + 48)
  count := blocksAt s (a + 72)
  placements := []
  stackLog := 0
  tableLogHeights := []

/-- The `Bytecode` the `Layout` at `a` points to. -/
def bytecodeOf (s : MachineState) (a : Word) : Word := s.getMem (a + 144)

/-- Every `Vec<BusBlock>`'s buffer, every block's coordinates and every coordinate form's terms
are read only. -/
structure BlocksRO (s : MachineState) (n : Nat) (ws : List (Word × Nat)) (p a : Word) : Prop where
  header : RO s n ws p a 24
  blocks : RO s n ws p (vecPtr s a) (48 * (vecLen s a).toNat)
  coordinates : ∀ i < (vecLen s a).toNat,
    FormRowsRO s n ws p (vecPtr s a + BitVec.ofNat 64 (48 * i)) 1

structure BusBalancePre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s busBalanceStack
  rodata : RodataOk s
  out : Region (s.getReg .x10) 120
  outFree : Outside s (s.getReg .x10) 120
  outStack : Apart (s.getReg .x10) 120 (stackLo s busBalanceStack) busBalanceStack
  outRodata : Apart (s.getReg .x10) 120 rodataBase rodataSize
  self : TranscriptOk s (s.getReg .x12)
  checked : byteAt s (s.getReg .x12 + 360) ≠ 0
  selfStack : Apart (s.getReg .x12) transcriptSize (stackLo s busBalanceStack) busBalanceStack
  selfOut : Apart (s.getReg .x12) transcriptSize (s.getReg .x10) 120
  selfFree : Outside s (s.getReg .x12) transcriptSize
  selfRodata : Apart (s.getReg .x12) transcriptSize rodataBase rodataSize
  proofStack : ProofApart s (s.getReg .x12) (stackLo s busBalanceStack) busBalanceStack
  proofOut : ProofApart s (s.getReg .x12) (s.getReg .x10) 120
  proofFree : Outside s (proofAt s (s.getReg .x12)) 48
  streamFree : Outside s (streamPtr s (s.getReg .x12)) (24 * streamLen s (s.getReg .x12))
  layout : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (s.getReg .x11) 168
  push : BlocksRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (s.getReg .x11 + 24)
  pull : BlocksRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (s.getReg .x11 + 48)
  count : BlocksRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (s.getReg .x11 + 72)
  /-- The layout's tables are the statement's, their padding rows read only. -/
  tablesLen : (vecLen s (s.getReg .x11)).toNat = tables.length
  tablesRO : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (vecPtr s (s.getReg .x11))
    (80 * tables.length)
  padding : ∀ i < tables.length,
    vecEs s (vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (80 * i)) = (tables.getD i default).padding
  paddingRO : ∀ i < tables.length,
    RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12)
      (vecPtr s (vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (80 * i)))
      (24 * (vecLen s (vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (80 * i))).toNat)

/-- The `ColumnClaim` at `a`. -/
def claimAt (s : MachineState) (a : Word) : ColumnClaim :=
  ⟨(s.getMem (a + 24)).toNat, vecEs s a, eAt s (a + 32)⟩

/-- `n` bytes from `p`, aligned, ending below `NEXT` at `t`, and allocated from `s` on unless
empty (an empty buffer's pointer still lies below `NEXT`, as `Outside` wants of an empty slice). -/
@[rv_addr] def BufIn (s t : MachineState) (p : Word) (n : Nat) : Prop :=
  p.toNat % 8 = 0 ∧ p.toNat + n ≤ heapNext t ∧ (n = 0 ∨ heapNext s ≤ p.toNat)

/-- Piece `j` of the forms' row `i` from `P`, its pointer and length in bytes: form `j`'s terms
(`j < 3`), or the row's own buffer (`j = 3`). -/
def formPiece (t : MachineState) (P : Word) (i j : Nat) : Word × Nat :=
  if j < 3 then
    (vecPtr t (vecPtr t (P + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j)),
      48 * (vecLen t (vecPtr t (P + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j))).toNat)
  else (vecPtr t (P + BitVec.ofNat 64 (24 * i)), 24 * (vecLen t (P + BitVec.ofNat 64 (24 * i))).toNat)

/-- The `BusResult` at `a` holds `r`, every buffer allocated from `s` on. -/
structure BusResultAt (s t : MachineState) (a : Word) (r : BusResultRust) : Prop where
  claims : VecOk t a 56 8 ∧ NewBuf s t (vecPtr t a) (56 * (vecCap t a).toNat) 8 ∧
    (List.range (vecLen t a).toNat).map
      (fun i ↦ claimAt t (vecPtr t a + BitVec.ofNat 64 (56 * i))) = r.claims ∧
    ∀ i < (vecLen t a).toNat, ∃ xs, NewVecE s t (vecPtr t a + BitVec.ofNat 64 (56 * i)) xs
  bytecodePoint : NewVecE s t (a + 24) r.bytecodePoint
  point : NewVecE s t (a + 48) r.point
  forms : VecOk t (a + 72) 24 8 ∧
    formRowsAt t (vecPtr t (a + 72)) (vecLen t (a + 72)).toNat = r.forms
  totals : NewVecE s t (a + 96) r.totals
  /-- The claims' buffer, and each claim's point's, which misses it (the caller fills its spare
  room in place). -/
  claimsIn : BufIn s t (vecPtr t a) (56 * (vecCap t a).toNat)
  claimPoints : ∀ i < (vecLen t a).toNat,
    BufIn s t (vecPtr t (vecPtr t a + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen t (vecPtr t a + BitVec.ofNat 64 (56 * i))).toNat) ∧
    Apart (vecPtr t (vecPtr t a + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen t (vecPtr t a + BitVec.ofNat 64 (56 * i))).toNat)
      (vecPtr t a) (56 * (vecCap t a).toNat)
  pointIn : BufIn s t (vecPtr t (a + 48)) (24 * (vecLen t (a + 48)).toNat)
  /-- The forms' buffer, its rows of three forms, every row's and every form's buffer, pairwise
  apart and apart from the forms' buffer. -/
  formsIn : BufIn s t (vecPtr t (a + 72)) (24 * (vecLen t (a + 72)).toNat)
  formRows : ∀ i < (vecLen t (a + 72)).toNat,
    vecLen t (vecPtr t (a + 72) + BitVec.ofNat 64 (24 * i)) = 3 ∧
    ∀ j ≤ 3, BufIn s t (formPiece t (vecPtr t (a + 72)) i j).1 (formPiece t (vecPtr t (a + 72)) i j).2
  formsApart : ∀ i < (vecLen t (a + 72)).toNat, ∀ j ≤ 3,
    Apart (formPiece t (vecPtr t (a + 72)) i j).1 (formPiece t (vecPtr t (a + 72)) i j).2
      (vecPtr t (a + 72)) (24 * (vecLen t (a + 72)).toNat) ∧
    ∀ i' < (vecLen t (a + 72)).toNat, ∀ j' ≤ 3, (i ≠ i' ∨ j ≠ j') →
      Apart (formPiece t (vecPtr t (a + 72)) i j).1 (formPiece t (vecPtr t (a + 72)) i j).2
        (formPiece t (vecPtr t (a + 72)) i' j').1 (formPiece t (vecPtr t (a + 72)) i' j').2

/-- `Ok(result)` exactly when `verifyBusBalanceM` returns it on the layout's values, `bev s bc`
being what `Bytecode::evaluate` computes for the `Bytecode` at `bc`; otherwise `Err` (`errNiche`
in the first capacity). Memory changes only in the result, the transcript's sponge and offsets,
the stack, `NEXT` and the heap allocated. -/
structure BusBalancePost (bev : MachineState → Word → List E → Option E)
    (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x12) T →
    match (verifyBusBalanceM (bev s (bytecodeOf s (s.getReg .x11)))
        (busLayoutAt s (s.getReg .x11))).run T with
    | some (r, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧
        BusResultAt s t (s.getReg .x10) r ∧ TranscriptAt t (s.getReg .x12) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 120 ∨ Within a (s.getReg .x12 + 8) 344 ∨
    Within a (stackLo s busBalanceStack) busBalanceStack ∨ Within a nextAddr 8 ∨ Fresh s t a

/-- `BusBalancePre`, and the `Bytecode` as `Bytecode::evaluate` reads it (`BcOk`, for a callee
with an `n`-byte stack). -/
structure BusBalancePreB (BcOk : MachineState → Nat → Word → Prop) (s : MachineState) : Prop
    extends BusBalancePre s where
  bytecode : BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11))

abbrev BusBalanceSpec (BcOk : MachineState → Nat → Word → Prop)
    (bev : MachineState → Word → List E → Option E) : Prop :=
  FunSpec Image.code 0x80006428 (BusBalancePreB BcOk) (BusBalancePost bev)

end Rv64Verifier.Bus
