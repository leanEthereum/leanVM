import Rv64Verifier.Proofs.Transcript.Repr
import Rv64Verifier.Proofs.Contracts
import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Proofs.Hash.Contracts

/-!
# Contracts of the transcript's functions

`transcript.rs`'s functions as compiled: each says the machine computes the `TM` mirror
(`Model/Transcript.lean`) on the transcript it is given, `Err` exactly when the mirror fails
(`none`). `Transcript::sample` is inlined into its callers (`samples`, `sumcheck`): a `duplex`,
then the state's first three lanes.

The callees' contracts this file states are hypotheses of the proofs: `ConcatSpec`
(`[Vec<E>; 2]::concat`) and `PolyEvalSpec` (`multilinear::poly_eval`). The others are stated where
they are proved: `keccak_f`'s in `Proofs/Hash/Contracts.lean` (`Contracts.KeccakFSpec`), the
runtime's (`memcpy`, `memset`, the allocator, `Vec` growth) in `Runtime/Contracts.lean`, `E`'s
product in `Proofs/Contracts.lean`.

Every contract asks for `.rodata` in place (`keccak_f` and `mul` read their tables from it), for
its stack as the runtime's (`RtStack`: above the heap, apart from `NEXT` and `.rodata`), and for the
regions it writes to lie apart from each other, from the stack, from `.rodata` and from the
proof's bytes; a function that allocates asks for the heap in shape (`HeapOk`) and for what it
writes and reads to lie outside the free heap (`Outside`).
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Contracts

/-! ## `Sponge::duplex`, at `0x80007cd8` -/

@[rv_addr] def duplexStack : Nat := 224 + keccakFStack

/-- `a0` = the sponge. -/
structure DuplexPre (s : MachineState) : Prop where
  sponge : Region (s.getReg .x10) 336
  stack : RtStack s duplexStack
  spongeStack : Apart (s.getReg .x10) 336 (stackLo s duplexStack) duplexStack
  rodata : RodataOk s
  spongeRodata : Apart (s.getReg .x10) 336 rodataBase rodataSize

/-- The sponge is permuted; memory changes only in the sponge and the stack. -/
structure DuplexPost (s t : MachineState) : Prop where
  value : spongeAt t (s.getReg .x10) = spDuplex (spongeAt s (s.getReg .x10))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 336 ∨
    Within a (stackLo s duplexStack) duplexStack

abbrev DuplexSpec : Prop := FunSpec Image.code 0x80007cd8 DuplexPre DuplexPost

/-! ## `Sponge::absorb`, at `0x8000c808` -/

@[rv_addr] def absorbStack : Nat := 32 + duplexStack

/-- `a0` = the sponge, `a1` = the scalar (by reference), `a2` = the tag. -/
structure AbsorbPre (s : MachineState) : Prop where
  sponge : Region (s.getReg .x10) 336
  value : Region (s.getReg .x11) 24
  stack : RtStack s absorbStack
  spongeStack : Apart (s.getReg .x10) 336 (stackLo s absorbStack) absorbStack
  valueStack : Apart (s.getReg .x11) 24 (stackLo s absorbStack) absorbStack
  valueSponge : Apart (s.getReg .x11) 24 (s.getReg .x10) 336
  rodata : RodataOk s
  spongeRodata : Apart (s.getReg .x10) 336 rodataBase rodataSize

/-- The scalar is absorbed with the tag; memory changes only in the sponge and the stack. -/
structure AbsorbPost (s t : MachineState) : Prop where
  value : spongeAt t (s.getReg .x10) =
    spAbsorb (spongeAt s (s.getReg .x10)) (eAt s (s.getReg .x11)) (s.getReg .x12).toNat
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 336 ∨
    Within a (stackLo s absorbStack) absorbStack

abbrev AbsorbSpec : Prop := FunSpec Image.code 0x8000c808 AbsorbPre AbsorbPost

/-! ## `Transcript::next_scalar`, at `0x8000c720` -/

@[rv_addr] def nextScalarStack : Nat := 64 + absorbStack

/-- `a0` = the `Result<E, VerifierError>` (tag, then the value or the error), `a1` = the
transcript. -/
structure NextScalarPre (s : MachineState) : Prop where
  out : Region (s.getReg .x10) 32
  self : TranscriptOk s (s.getReg .x11)
  stack : RtStack s nextScalarStack
  outStack : Apart (s.getReg .x10) 32 (stackLo s nextScalarStack) nextScalarStack
  selfStack : Apart (s.getReg .x11) transcriptSize (stackLo s nextScalarStack) nextScalarStack
  outSelf : Apart (s.getReg .x10) 32 (s.getReg .x11) transcriptSize
  proofStack : ProofApart s (s.getReg .x11) (stackLo s nextScalarStack) nextScalarStack
  proofOut : ProofApart s (s.getReg .x11) (s.getReg .x10) 32
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) 32 rodataBase rodataSize
  selfRodata : Apart (s.getReg .x11) transcriptSize rodataBase rodataSize

/-- `Ok` (tag `0`) with the scalar exactly when `TM.nextScalar` returns it, the transcript then
standing for the mirror's; otherwise `Err(StreamExhausted)` (tag `1`, discriminant `3`). Memory
changes only in the result, the sponge and offsets, and the stack. -/
structure NextScalarPost (s t : MachineState) : Prop where
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match TM.nextScalar.run T with
    | some (x, T') => t.getMem (s.getReg .x10) = 0 ∧ eAt t (s.getReg .x10 + 8) = x ∧
        TranscriptAt t (s.getReg .x11) T'
    | none => t.getMem (s.getReg .x10) = 1 ∧ t.getMem (s.getReg .x10 + 8) = 3
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s nextScalarStack) nextScalarStack

abbrev NextScalarSpec : Prop := FunSpec Image.code 0x8000c720 NextScalarPre NextScalarPost

/-! ## `GenericShunt<Map<Range<usize>, next_scalars::{closure}>, Result<!, _>>::next`, at
`0x80011ef4`

The iterator is `(transcript, start, end, residual)`; `next` returns `Option<E>` (tag `1` for
`Some`, then the value). -/

@[rv_addr] def shuntNextStack : Nat := 64 + nextScalarStack

/-- The shunt's transcript, range and residual. -/
def shuntP (s : MachineState) : Word := s.getMem (s.getReg .x11)
def shuntStart (s : MachineState) : Word := s.getMem (s.getReg .x11 + 8)
def shuntEnd (s : MachineState) : Word := s.getMem (s.getReg .x11 + 16)
def shuntR (s : MachineState) : Word := s.getMem (s.getReg .x11 + 24)

/-- `a0` = the `Option<E>`, `a1` = the shunt. -/
structure ShuntNextPre (s : MachineState) : Prop where
  out : Region (s.getReg .x10) 32
  shunt : Region (s.getReg .x11) 32
  residual : Region (shuntR s) 16
  self : TranscriptOk s (shuntP s)
  stack : RtStack s shuntNextStack
  outStack : Apart (s.getReg .x10) 32 (stackLo s shuntNextStack) shuntNextStack
  shuntStack : Apart (s.getReg .x11) 32 (stackLo s shuntNextStack) shuntNextStack
  residualStack : Apart (shuntR s) 16 (stackLo s shuntNextStack) shuntNextStack
  selfStack : Apart (shuntP s) transcriptSize (stackLo s shuntNextStack) shuntNextStack
  outShunt : Apart (s.getReg .x10) 32 (s.getReg .x11) 32
  outResidual : Apart (s.getReg .x10) 32 (shuntR s) 16
  outSelf : Apart (s.getReg .x10) 32 (shuntP s) transcriptSize
  shuntResidual : Apart (s.getReg .x11) 32 (shuntR s) 16
  shuntSelf : Apart (s.getReg .x11) 32 (shuntP s) transcriptSize
  residualSelf : Apart (shuntR s) 16 (shuntP s) transcriptSize
  proofStack : ProofApart s (shuntP s) (stackLo s shuntNextStack) shuntNextStack
  proofOut : ProofApart s (shuntP s) (s.getReg .x10) 32
  proofShunt : ProofApart s (shuntP s) (s.getReg .x11) 32
  proofResidual : ProofApart s (shuntP s) (shuntR s) 16
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) 32 rodataBase rodataSize
  shuntRodata : Apart (s.getReg .x11) 32 rodataBase rodataSize
  residualRodata : Apart (shuntR s) 16 rodataBase rodataSize
  selfRodata : Apart (shuntP s) transcriptSize rodataBase rodataSize

/-- Past the end, `None` and nothing changes; before it, `start` advances and `next_scalar` runs:
`Some` with its scalar, or `None` with its error (`3`) in the residual. Memory changes only in
the result, `start`, the residual, the sponge and offsets, and the stack. -/
structure ShuntNextPost (s t : MachineState) : Prop where
  value : ∀ T, TranscriptAt s (shuntP s) T →
    if (shuntStart s).toNat < (shuntEnd s).toNat then
      t.getMem (s.getReg .x11 + 8) = shuntStart s + 1 ∧
      match TM.nextScalar.run T with
      | some (x, T') => t.getMem (s.getReg .x10) = 1 ∧ eAt t (s.getReg .x10 + 8) = x ∧
          TranscriptAt t (shuntP s) T'
      | none => t.getMem (s.getReg .x10) = 0 ∧ t.getMem (shuntR s) = 3
    else t.getMem (s.getReg .x10) = 0 ∧ t.getMem (s.getReg .x11 + 8) = shuntStart s ∧
      TranscriptAt t (shuntP s) T
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨ Within a (s.getReg .x11 + 8) 8 ∨
    Within a (shuntR s) 16 ∨ Within a (shuntP s + 8) 344 ∨
    Within a (stackLo s shuntNextStack) shuntNextStack

abbrev ShuntNextSpec : Prop := FunSpec Image.code 0x80011ef4 ShuntNextPre ShuntNextPost

/-! ## Functions that allocate

`a0` is where the result goes, `a1` the transcript; the result's buffer is new, and memory changes
only in the result, the sponge and offsets, the stack, `NEXT` and the heap allocated. -/

/-- What every allocating function asks of the result at `a0` (`n` bytes), the transcript at
`a1`, the proof and its stack (`k` bytes). -/
structure TPre (n k : Nat) (s : MachineState) : Prop where
  heap : HeapOk s
  out : Region (s.getReg .x10) n
  self : TranscriptOk s (s.getReg .x11)
  stack : RtStack s k
  outStack : Apart (s.getReg .x10) n (stackLo s k) k
  selfStack : Apart (s.getReg .x11) transcriptSize (stackLo s k) k
  outSelf : Apart (s.getReg .x10) n (s.getReg .x11) transcriptSize
  proofStack : ProofApart s (s.getReg .x11) (stackLo s k) k
  proofOut : ProofApart s (s.getReg .x11) (s.getReg .x10) n
  outFree : Outside s (s.getReg .x10) n
  selfFree : Outside s (s.getReg .x11) transcriptSize
  proofFree : Outside s (proofAt s (s.getReg .x11)) 48
  streamFree : Outside s (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11))
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) n rodataBase rodataSize
  selfRodata : Apart (s.getReg .x11) transcriptSize rodataBase rodataSize

/-- The frame of an allocating function: the result (`n` bytes), the transcript's sponge and
offsets, its stack (`k` bytes), `NEXT` and the heap allocated. -/
def TFrame (n k : Nat) (s t : MachineState) : Prop :=
  DFrame s t fun a ↦ Within a (s.getReg .x10) n ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s k) k ∨ Within a nextAddr 8 ∨ Fresh s t a

/-- `Vec::reserve` (`Runtime.ReserveSpec`) whose buffer afterwards is the same one, or a new one: a
`Vec` filled after the call writes only memory allocated since. The runtime's contract does not say
so yet; this is what the transcript's proofs assume. -/
def ReserveFreshSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (ReservePre size align) fun s t ↦ ReservePost size align s t ∧
    ((vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10) ∧
      vecCap t (s.getReg .x10) = vecCap s (s.getReg .x10)) ∨
     NewBuf s t (vecPtr t (s.getReg .x10)) ((vecCap t (s.getReg .x10)).toNat * size) align)

/-- `RawVec::grow_one` (`Runtime.GrowOneSpec`) whose new buffer is new. -/
def GrowOneFreshSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (GrowOnePre size align) fun s t ↦ GrowOnePost size align s t ∧
    NewBuf s t (vecPtr t (s.getReg .x10)) ((vecCap t (s.getReg .x10)).toNat * size) align

/-! ### `Transcript::next_scalars`, at `0x80004818` -/

@[rv_addr] def nextScalarsStack : Nat := 224 + shuntNextStack

/-- `a2` = how many. -/
abbrev NextScalarsPre : MachineState → Prop := TPre 24 nextScalarsStack

/-- `Ok(xs)` exactly when `TM.nextScalars` returns `xs`, the transcript then standing for the
mirror's; otherwise `Err` (`errNiche` in the capacity). -/
structure NextScalarsPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (TM.nextScalars (s.getReg .x12).toNat).run T with
    | some (xs, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧ NewVecE s t (s.getReg .x10) xs ∧
        TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : TFrame 24 nextScalarsStack s t

abbrev NextScalarsSpec : Prop := FunSpec Image.code 0x80004818 NextScalarsPre NextScalarsPost

/-! ### `Transcript::samples`, at `0x8000c618` -/

@[rv_addr] def samplesStack : Nat := 80 + duplexStack

/-- `a2` = how many. -/
abbrev SamplesPre : MachineState → Prop := TPre 24 samplesStack

/-- The `Vec` of what `TM.samples` returns, the transcript then standing for the mirror's. -/
structure SamplesPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ xs T',
    (TM.samples (s.getReg .x12).toNat).run T = some (xs, T') ∧ NewVecE s t (s.getReg .x10) xs ∧
      TranscriptAt t (s.getReg .x11) T'
  frame : TFrame 24 samplesStack s t

abbrev SamplesSpec : Prop := FunSpec Image.code 0x8000c618 SamplesPre SamplesPost

/-! ### `[Vec<E>; 2]::concat`, at `0x8000eea4` -/

@[rv_addr] def concatStack : Nat := 272

/-- `a0` = the result, `a1` = the two `Vec`s. -/
structure ConcatPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : Region (s.getReg .x10) 24
  parts : Region (s.getReg .x11) 48
  left : VecOk s (s.getReg .x11) 24 8
  right : VecOk s (s.getReg .x11 + 24) 24 8
  stack : RtStack s concatStack
  outStack : Apart (s.getReg .x10) 24 (stackLo s concatStack) concatStack
  partsStack : Apart (s.getReg .x11) 48 (stackLo s concatStack) concatStack
  outFree : Outside s (s.getReg .x10) 24
  partsFree : Outside s (s.getReg .x11) 48

/-- A new `Vec` of both parts' elements. -/
structure ConcatPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : NewVecE s t (s.getReg .x10) (vecEs s (s.getReg .x11) ++ vecEs s (s.getReg .x11 + 24))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s concatStack) concatStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev ConcatSpec : Prop := FunSpec Image.code 0x8000eea4 ConcatPre ConcatPost

/-! ### `Transcript::sumcheck_round_poly`, at `0x8000c334` -/

@[rv_addr] def roundPolyStack : Nat := 160 + nextScalarsStack

/-- `a2` = `count` (at least two), `a3` = `claim` and `a4` = `eq_factor` (an `Option<E>`), by
reference. -/
structure RoundPolyPre (s : MachineState) : Prop extends TPre 24 roundPolyStack s where
  count : 2 ≤ (s.getReg .x12).toNat
  claim : Region (s.getReg .x13) 24
  eqFactor : Region (s.getReg .x14) 32
  claimFree : Outside s (s.getReg .x13) 24
  eqFactorFree : Outside s (s.getReg .x14) 32
  claimStack : Apart (s.getReg .x13) 24 (stackLo s roundPolyStack) roundPolyStack
  eqFactorStack : Apart (s.getReg .x14) 32 (stackLo s roundPolyStack) roundPolyStack
  claimSelf : Apart (s.getReg .x13) 24 (s.getReg .x11) transcriptSize
  eqFactorSelf : Apart (s.getReg .x14) 32 (s.getReg .x11) transcriptSize

/-- `Ok` with the round polynomial exactly when `TM.sumcheckRoundPoly` returns it. -/
structure RoundPolyPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (TM.sumcheckRoundPoly (s.getReg .x12).toNat (eAt s (s.getReg .x13))
        (optEAt s (s.getReg .x14))).run T with
    | some (q, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧ NewVecE s t (s.getReg .x10) q ∧
        TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : TFrame 24 roundPolyStack s t

abbrev RoundPolySpec : Prop := FunSpec Image.code 0x8000c334 RoundPolyPre RoundPolyPost

/-! ### `multilinear::poly_eval`, at `0x8000cef4` -/

@[rv_addr] def polyEvalStack : Nat := 96 + mulStack

/-- `a0` = the result, `a1`/`a2` = the coefficients, `a3` = the point. -/
structure PolyEvalPre (s : MachineState) : Prop where
  out : Region (s.getReg .x10) 24
  coeffs : (s.getReg .x12).toNat = 0 ∨ Region (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  point : Region (s.getReg .x13) 24
  stack : RtStack s polyEvalStack
  outStack : Apart (s.getReg .x10) 24 (stackLo s polyEvalStack) polyEvalStack
  coeffsStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s polyEvalStack)
    polyEvalStack
  pointStack : Apart (s.getReg .x13) 24 (stackLo s polyEvalStack) polyEvalStack
  outCoeffs : Apart (s.getReg .x10) 24 (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  outPoint : Apart (s.getReg .x10) 24 (s.getReg .x13) 24
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize

/-- The polynomial at the point; memory changes only in the result and the stack. -/
structure PolyEvalPost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) =
    polyEvalRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat) (eAt s (s.getReg .x13))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s polyEvalStack) polyEvalStack

abbrev PolyEvalSpec : Prop := FunSpec Image.code 0x8000cef4 PolyEvalPre PolyEvalPost

/-! ### `transcript::sumcheck`, at `0x80010538` -/

@[rv_addr] def sumcheckStack : Nat := 208 + roundPolyStack

/-- `a0` = the `Result<(Vec<E>, E), _>` (48 bytes), `a2` = `claim` (by reference: the function
overwrites it), `a3` = `count` (at least two), `a4`/`a5` = `equalities`. -/
structure SumcheckPre (s : MachineState) : Prop extends TPre 48 sumcheckStack s where
  count : 2 ≤ (s.getReg .x13).toNat
  claim : Region (s.getReg .x12) 24
  eqs : (s.getReg .x15).toNat = 0 ∨ Region (s.getReg .x14) (32 * (s.getReg .x15).toNat)
  claimFree : Outside s (s.getReg .x12) 24
  eqsFree : Outside s (s.getReg .x14) (32 * (s.getReg .x15).toNat)
  claimStack : Apart (s.getReg .x12) 24 (stackLo s sumcheckStack) sumcheckStack
  eqsStack : Apart (s.getReg .x14) (32 * (s.getReg .x15).toNat) (stackLo s sumcheckStack)
    sumcheckStack
  claimSelf : Apart (s.getReg .x12) 24 (s.getReg .x11) transcriptSize
  eqsSelf : Apart (s.getReg .x14) (32 * (s.getReg .x15).toNat) (s.getReg .x11) transcriptSize
  claimOut : Apart (s.getReg .x12) 24 (s.getReg .x10) 48
  eqsOut : Apart (s.getReg .x14) (32 * (s.getReg .x15).toNat) (s.getReg .x10) 48
  claimEqs : Apart (s.getReg .x12) 24 (s.getReg .x14) (32 * (s.getReg .x15).toNat)
  proofClaim : ProofApart s (s.getReg .x11) (s.getReg .x12) 24
  claimRodata : Apart (s.getReg .x12) 24 rodataBase rodataSize

/-- `Ok((point, claim))` exactly when `TM.sumcheck` returns it. -/
structure SumcheckPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (TM.sumcheck (eAt s (s.getReg .x12)) (s.getReg .x13).toNat
        (optEListAt s (s.getReg .x14) (s.getReg .x15).toNat)).run T with
    | some ((point, claim), T') => vecCap t (s.getReg .x10) ≠ errNiche ∧
        NewVecE s t (s.getReg .x10) point ∧ eAt t (s.getReg .x10 + 24) = claim ∧
        TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 48 ∨ Within a (s.getReg .x12) 24 ∨
    Within a (s.getReg .x11 + 8) 344 ∨ Within a (stackLo s sumcheckStack) sumcheckStack ∨
    Within a nextAddr 8 ∨ Fresh s t a

abbrev SumcheckSpec : Prop := FunSpec Image.code 0x80010538 SumcheckPre SumcheckPost

end Rv64Verifier.Transcript
