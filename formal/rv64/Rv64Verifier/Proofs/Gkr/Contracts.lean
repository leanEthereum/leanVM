import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Model.KeccakGkr

/-!
# Contracts of the Keccak reduction

`keccak.rs`'s `open`, `verify_layer` and `verify_keccak` as compiled: each says that when the
function returns `Ok`, what it returns and the transcript it leaves are its mirror's in
`Model/KeccakGkr.lean` (`openRust`, `verifyLayerRust`, `verifyKeccakRust`), and that it returns `Err`
when the mirror fails (`none`); a panic is a trap, a dead end. The callees these functions need
that no other file states are stated here as hypotheses of the proofs: `vec![None; n]` of
`Option<E>` (`OptFromElemSpec`) and `eq_kernel` (`EqKernelSpec`).

How the image holds the values, read off the code:

* `Claim` (96 bytes): `mu`, `point`, `weights` as `Vec<E>` at `0`, `24`, `48`, `value` at `72`
  (`claimAt`).
* `open`'s `Result<(Vec<E>, [E; 64], E), VerifierError>` (1584 bytes): the slot `Vec` at `0` (its
  capacity `errNiche` for `Err`), the row at `24`, the value at `1560`.
* `verify_layer`'s `Result<Claim, VerifierError>`: the claim, `Err` in the capacity of `mu`.
* `KeccakOpenings` (96 bytes): the input point and slices at `0` and `24`, then the outputs, an
  `Option<(Vec<E>, E)>` at `48` whose `None` is `errNiche` in the capacity, the word at `72`;
  `Err` is `errNiche` in the capacity at `0`.
* `Transcript::checked` is the byte at `360`: the functions that check something test it, and
  their contracts ask for checked mode, the mode `verify_execution` runs (the mirrors check).

The shape's depth is `KECCAK_DEPTH = 12`, the only one the caller passes and the one the mirrors'
simulations are proved at. `output` has `STATE_LANES = 25` elements at every call: the compiled
`verify_keccak` does not test its length (the compiler propagated the callers' constant), so its
contract asks for it.
-/

namespace Rv64Verifier.Gkr
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts

/-! ## Values in memory -/

/-- The `Claim` at `c`. -/
def claimAt (s : MachineState) (c : Word) : KeccakClaim :=
  ⟨eAt s (c + 72), vecEs s c, vecEs s (c + 24), vecEs s (c + 48)⟩

/-- The `n` bytes of the elements of the `Vec<E>` at `a` lie in memory, if any. -/
@[rv_addr] def VecRegion (s : MachineState) (a : Word) : Prop :=
  (vecLen s a).toNat = 0 ∨ Region (vecPtr s a) (24 * (vecLen s a).toNat)

/-- The elements of the `Vec<E>` at `a` miss the `n` bytes from `lo`. -/
@[rv_addr] def VecApart (s : MachineState) (a : Word) (lo : Word) (n : Nat) : Prop :=
  Apart (vecPtr s a) (24 * (vecLen s a).toNat) lo n

/-- The elements of the `Vec<E>` at `a` miss the free heap. -/
@[rv_addr] def VecOutside (s : MachineState) (a : Word) : Prop :=
  Outside s (vecPtr s a) (24 * (vecLen s a).toNat)

/-- The transcript's `checked` flag is set. -/
def Checked (s : MachineState) (p : Word) : Prop := byteAt s (p + 360) ≠ 0

/-! ## `<Option<E> as SpecFromElem>::from_elem` (`vec![x; n]`), at `0x80010724` -/

@[rv_addr] def optFromElemStack : Nat := 80 + reserveStack

/-- `a0` = where the `Vec` goes, `a1` = the element (an `Option<E>`, 32 bytes, by reference),
`a2` = `n`. -/
structure OptFromElemPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : Region (s.getReg .x10) 24
  elem : Region (s.getReg .x11) 32
  stack : RtStack s optFromElemStack
  outFree : Outside s (s.getReg .x10) 24
  elemFree : Outside s (s.getReg .x11) 32
  outStack : Apart (s.getReg .x10) 24 (stackLo s optFromElemStack) optFromElemStack
  elemStack : Apart (s.getReg .x11) 32 (stackLo s optFromElemStack) optFromElemStack
  elemOut : Apart (s.getReg .x11) 32 (s.getReg .x10) 24

/-- A new `Vec` of `n` copies of the element; memory changes only in the `Vec`, the stack, `NEXT`
and the new allocation. -/
structure OptFromElemPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 32 8
  len : vecLen t (s.getReg .x10) = s.getReg .x12
  elems : optEListAt t (vecPtr t (s.getReg .x10)) (s.getReg .x12).toNat =
    List.replicate (s.getReg .x12).toNat (optEAt s (s.getReg .x11))
  fresh : NewBuf s t (vecPtr t (s.getReg .x10)) (32 * (s.getReg .x12).toNat) 8
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s optFromElemStack) optFromElemStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev OptFromElemSpec : Prop := FunSpec Image.code 0x80010724 OptFromElemPre OptFromElemPost

/-! ## `multilinear::eq_kernel`, at `0x8000cb38` -/

@[rv_addr] def eqKernelStack : Nat := 208 + mulStack

/-- `a0` = where the `Vec` goes, `a1`/`a2` = the point. -/
structure EqKernelPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : Region (s.getReg .x10) 24
  point : (s.getReg .x12).toNat = 0 ∨ Region (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  stack : RtStack s eqKernelStack
  outFree : Outside s (s.getReg .x10) 24
  pointFree : (s.getReg .x12).toNat = 0 ∨ Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  outStack : Apart (s.getReg .x10) 24 (stackLo s eqKernelStack) eqKernelStack
  pointStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s eqKernelStack)
    eqKernelStack
  pointOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  rodata : RodataOk s
  outRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize

/-- A new `Vec` of `eqKernelRust` of the point; memory changes only in the `Vec`, the stack,
`NEXT` and the new allocation. -/
structure EqKernelPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : NewVecE s t (s.getReg .x10) (eqKernelRust (eListAt s (s.getReg .x11) (s.getReg .x12).toNat))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s eqKernelStack) eqKernelStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev EqKernelSpec : Prop := FunSpec Image.code 0x8000cb38 EqKernelPre EqKernelPost

/-! ## `keccak::open`, at `0x80010184` -/

@[rv_addr] def openStack : Nat := 1856 + sumcheckStack

/-- The registers of `open(transcript, shape, claim, first, count, value)`: `a0` the result,
`a1` the transcript, `a2`/`a3` the shape, `a4` the claim, `a5`/`a6` `first` and `count`, `a7` the
value, by reference (`sumcheck` overwrites it). -/
@[rv_addr] def oOut (s : MachineState) : Word := s.getReg .x10
@[rv_addr] def oP (s : MachineState) : Word := s.getReg .x11
@[rv_addr] def oClaim (s : MachineState) : Word := s.getReg .x14
@[rv_addr] def oValue (s : MachineState) : Word := s.getReg .x17

/-- The shape at `a2`/`a3`. -/
def shapeOf (s : MachineState) : KeccakShape := ⟨(s.getReg .x12).toNat, (s.getReg .x13).toNat⟩

/-- The result (1584 bytes), the transcript, the claim, its point and weights, the value: in
memory, the parts written apart from everything else, read-only parts apart from what is written,
and outside the free heap; `first + count` at most the two segments. -/
structure OpenPre (s : MachineState) : Prop extends TPre 1584 openStack s where
  depth : s.getReg .x13 = 12
  firstCount : (s.getReg .x15).toNat + (s.getReg .x16).toNat ≤ 2
  claim : Region (oClaim s) 96
  point : VecRegion s (oClaim s + 24)
  weights : VecRegion s (oClaim s + 48)
  value : Region (oValue s) 24
  claimFree : Outside s (oClaim s) 96
  pointFree : VecOutside s (oClaim s + 24)
  weightsFree : VecOutside s (oClaim s + 48)
  valueFree : Outside s (oValue s) 24
  claimStack : Apart (oClaim s) 96 (stackLo s openStack) openStack
  pointStack : VecApart s (oClaim s + 24) (stackLo s openStack) openStack
  weightsStack : VecApart s (oClaim s + 48) (stackLo s openStack) openStack
  valueStack : Apart (oValue s) 24 (stackLo s openStack) openStack
  claimOut : Apart (oClaim s) 96 (oOut s) 1584
  pointOut : VecApart s (oClaim s + 24) (oOut s) 1584
  weightsOut : VecApart s (oClaim s + 48) (oOut s) 1584
  valueOut : Apart (oValue s) 24 (oOut s) 1584
  claimSelf : Apart (oClaim s) 96 (oP s + 8) 344
  pointSelf : VecApart s (oClaim s + 24) (oP s + 8) 344
  weightsSelf : VecApart s (oClaim s + 48) (oP s + 8) 344
  valueSelf : Apart (oValue s) 24 (oP s) transcriptSize
  claimValue : Apart (oClaim s) 96 (oValue s) 24
  pointValue : VecApart s (oClaim s + 24) (oValue s) 24
  weightsValue : VecApart s (oClaim s + 48) (oValue s) 24
  proofValue : ProofApart s (oP s) (oValue s) 24
  valueRodata : Apart (oValue s) 24 rodataBase rodataSize

/-- What `open` may write: the result, the value, the sponge and offsets, its stack, `NEXT` and
what it allocates. -/
@[rv_addr] def OpenW (s t : MachineState) (a : Word) : Prop :=
  Within a (oOut s) 1584 ∨ Within a (oValue s) 24 ∨ Within a (oP s + 8) 344 ∨
    Within a (stackLo s openStack) openStack ∨ Within a nextAddr 8 ∨ Fresh s t a

/-- `Ok((slot, row, value))` exactly when `openRust` returns it, the transcript then standing for
the mirror's; otherwise `Err`. -/
structure OpenPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (oP s) T →
    match (openRust (shapeOf s) (claimAt s (oClaim s)) (s.getReg .x15).toNat
        (s.getReg .x16).toNat (eAt s (oValue s))).run T with
    | some ((slot, row, v), T') => vecCap t (oOut s) ≠ errNiche ∧ NewVecE s t (oOut s) slot ∧
        eListAt t (oOut s + 24) 64 = row ∧ eAt t (oOut s + 1560) = v ∧ TranscriptAt t (oP s) T'
    | none => vecCap t (oOut s) = errNiche
  frame : DFrame s t (OpenW s t)

abbrev OpenSpec : Prop := FunSpec Image.code 0x80010184 OpenPre OpenPost

/-! ## `keccak::verify_layer`, at `0x8000f04c` -/

@[rv_addr] def verifyLayerStack : Nat := 1712 + sumcheckStack

/-- `a0` the result, `a1` the transcript, `a2`/`a3` the shape, `a4` `step`, `a5` the claim. -/
@[rv_addr] def lClaim (s : MachineState) : Word := s.getReg .x15

/-- The claim the function returns, at `a`: its three `Vec`s new since `s`. -/
structure ClaimOut (s t : MachineState) (a : Word) (c : KeccakClaim) : Prop where
  mu : NewVecE s t a c.mu
  point : NewVecE s t (a + 24) c.point
  weights : NewVecE s t (a + 48) c.weights
  value : eAt t (a + 72) = c.value

/-- The result (96 bytes), the transcript in checked mode and the claim with its three `Vec`s: in
memory, apart from what is written and outside the free heap. -/
structure VerifyLayerPre (s : MachineState) : Prop extends TPre 96 verifyLayerStack s where
  depth : s.getReg .x13 = 12
  step : (s.getReg .x14).toNat < 12
  checked : Checked s (s.getReg .x11)
  claim : Region (lClaim s) 96
  mu : VecRegion s (lClaim s)
  point : VecRegion s (lClaim s + 24)
  weights : VecRegion s (lClaim s + 48)
  claimFree : Outside s (lClaim s) 96
  muFree : VecOutside s (lClaim s)
  pointFree : VecOutside s (lClaim s + 24)
  weightsFree : VecOutside s (lClaim s + 48)
  claimStack : Apart (lClaim s) 96 (stackLo s verifyLayerStack) verifyLayerStack
  muStack : VecApart s (lClaim s) (stackLo s verifyLayerStack) verifyLayerStack
  pointStack : VecApart s (lClaim s + 24) (stackLo s verifyLayerStack) verifyLayerStack
  weightsStack : VecApart s (lClaim s + 48) (stackLo s verifyLayerStack) verifyLayerStack
  claimOut : Apart (lClaim s) 96 (s.getReg .x10) 96
  muOut : VecApart s (lClaim s) (s.getReg .x10) 96
  pointOut : VecApart s (lClaim s + 24) (s.getReg .x10) 96
  weightsOut : VecApart s (lClaim s + 48) (s.getReg .x10) 96
  claimSelf : Apart (lClaim s) 96 (s.getReg .x11 + 8) 344
  muSelf : VecApart s (lClaim s) (s.getReg .x11 + 8) 344
  pointSelf : VecApart s (lClaim s + 24) (s.getReg .x11 + 8) 344
  weightsSelf : VecApart s (lClaim s + 48) (s.getReg .x11 + 8) 344

/-- `Ok(claim)` exactly when `verifyLayerRust` returns it, the transcript then standing for the
mirror's; otherwise `Err`. -/
structure VerifyLayerPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (verifyLayerRust (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s))).run T with
    | some (c, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧ ClaimOut s t (s.getReg .x10) c ∧
        TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : TFrame 96 verifyLayerStack s t

abbrev VerifyLayerSpec : Prop := FunSpec Image.code 0x8000f04c VerifyLayerPre VerifyLayerPost

/-! ## `keccak::verify_keccak`, at `0x80008e34` -/

@[rv_addr] def verifyKeccakStack : Nat := 5248 + openStack

/-- `a0` the result, `a1` the transcript, `a2`/`a3` the shape, `a4`/`a5` `instance`, `a6`/`a7`
`output`. -/
@[rv_addr] def kInst (s : MachineState) : Word := s.getReg .x14
@[rv_addr] def kInstLen (s : MachineState) : Nat := (s.getReg .x15).toNat
@[rv_addr] def kOutput (s : MachineState) : Word := s.getReg .x16
@[rv_addr] def kOutputLen (s : MachineState) : Nat := (s.getReg .x17).toNat

/-- The outputs' `Option<(Vec<E>, E)>` at `a`: `None` is `errNiche` in the capacity. -/
def OutputsAt (s t : MachineState) (a : Word) : Option (List E × E) → Prop
  | none => vecCap t a = errNiche
  | some (point, word) => vecCap t a ≠ errNiche ∧ NewVecE s t a point ∧ eAt t (a + 24) = word

/-- The result (96 bytes), the transcript in checked mode, `instance` and `output`: in memory,
apart from what is written and outside the free heap. -/
structure VerifyKeccakPre (s : MachineState) : Prop extends TPre 96 verifyKeccakStack s where
  depth : s.getReg .x13 = 12
  checked : Checked s (s.getReg .x11)
  outputLen : kOutputLen s = 25
  inst : kInstLen s = 0 ∨ Region (kInst s) (24 * kInstLen s)
  output : kOutputLen s = 0 ∨ Region (kOutput s) (24 * kOutputLen s)
  instFree : Outside s (kInst s) (24 * kInstLen s)
  outputFree : Outside s (kOutput s) (24 * kOutputLen s)
  instStack : Apart (kInst s) (24 * kInstLen s) (stackLo s verifyKeccakStack) verifyKeccakStack
  outputStack : Apart (kOutput s) (24 * kOutputLen s) (stackLo s verifyKeccakStack)
    verifyKeccakStack
  instOut : Apart (kInst s) (24 * kInstLen s) (s.getReg .x10) 96
  outputOut : Apart (kOutput s) (24 * kOutputLen s) (s.getReg .x10) 96
  instSelf : Apart (kInst s) (24 * kInstLen s) (s.getReg .x11 + 8) 344
  outputSelf : Apart (kOutput s) (24 * kOutputLen s) (s.getReg .x11 + 8) 344

/-- `Ok(openings)` exactly when `verifyKeccakRust` returns them, the transcript then standing for
the mirror's; otherwise `Err`. -/
structure VerifyKeccakPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (verifyKeccakRust (shapeOf s) (eListAt s (kInst s) (kInstLen s))
        (eListAt s (kOutput s) (kOutputLen s))).run T with
    | some (o, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧
        NewVecE s t (s.getReg .x10) o.inputs.1 ∧ NewVecE s t (s.getReg .x10 + 24) o.inputs.2 ∧
        OutputsAt s t (s.getReg .x10 + 48) o.outputs ∧ TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : TFrame 96 verifyKeccakStack s t

abbrev VerifyKeccakSpec : Prop := FunSpec Image.code 0x80008e34 VerifyKeccakPre VerifyKeccakPost

end Rv64Verifier.Gkr
