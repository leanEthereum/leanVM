import Rv64Verifier.Proofs.Pcs.Common
import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Model.Whir
import Rv64Verifier.Model.Walk
import Rv64Verifier.Proofs.Transcript.Contracts

/-!
# Contracts of the opening's functions

`ring_switch.rs` and `lib.rs`'s `StackBasis` and `verify_stacked_opening` as compiled: each says
the machine computes its mirror in `Model/Whir.lean` (namespace `Model.Pcs`), which
`ringSwitchRust_sim` and `verifyStackedOpeningRust_sim` relate to the statement. A function that
traps (an `assert`, a slice out of bounds) reaches a dead end, which a `FunSpec` allows, so a
contract speaks only of the runs that return: the mirror then returns too (`some`), with the
machine's value.

How the image holds the values, read off the code:

* `RingWeight` (48 bytes): `point: Vec<E>` at `0`, `coefficients: Vec<E>` at `24`
  (`ringWeightAt`).
* `StackWeight` (64 bytes), its tag a niche in the first word: `0x8000000000000000` for `Eq`, its
  point a `Vec<E>` at `8`; `0x8000000000000001` for `Ring`, a `RingWeight` at `8`; any other word for
  `PlacedRing`, a `RingWeight` at `0` and the `Placement`'s `variables`, `index` at `48`, `56`
  (`stackWeightAt`). A `StackClaim` (88 bytes) is the weight, then its value at `64`.
* `StackBasis` (40 bytes): `scales: Vec<E>` at `0`, `claims: &[StackClaim]` at `24` (pointer and
  length).

Every contract states the bytes below `sp` it may use, its callees' included (`*Stack`), the
regions it reads (`Src`: apart from its stack, the free heap and `NEXT`) and writes (`Dst`), and
its frame on doublewords (`DFrame`).
-/

namespace Rv64Verifier.PcsContracts
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Transcript
  Rv64Verifier.Pcs Rv64Verifier.Model.Pcs Rv64Verifier.Contracts

/-! ## Values in memory -/

/-- The `RingWeight` at `a`. -/
def ringWeightAt (s : MachineState) (a : Word) : RingWeightRust := ⟨vecEs s a, vecEs s (a + 24)⟩

/-- The bytes read of the `RingWeight` at `a`: the struct and both buffers. -/
structure RingSrc (s : MachineState) (k : Nat) (a : Word) : Prop where
  self : Src s k a 48
  point : Src s k (vecPtr s a) (24 * (vecLen s a).toNat)
  coeffs : Src s k (vecPtr s (a + 24)) (24 * (vecLen s (a + 24)).toNat)

/-- `StackWeight::Eq`'s tag. -/
@[rv_addr] def eqTag : Word := 0x8000000000000000

/-- `StackWeight::Ring`'s tag. -/
@[rv_addr] def ringTag : Word := 0x8000000000000001

/-- The `StackWeight` at `a`. -/
def stackWeightAt (s : MachineState) (a : Word) : StackWeightRust :=
  if s.getMem a = eqTag then .eq (vecEs s (a + 8))
  else if s.getMem a = ringTag then .ring (ringWeightAt s (a + 8))
  else .placedRing ⟨(s.getMem (a + 48)).toNat, s.getMem (a + 56)⟩ (ringWeightAt s a)

/-- The bytes read of the `StackWeight` at `a`. -/
def WeightSrc (s : MachineState) (k : Nat) (a : Word) : Prop :=
  Src s k a 64 ∧
    if s.getMem a = eqTag then Src s k (vecPtr s (a + 8)) (24 * (vecLen s (a + 8)).toNat)
    else if s.getMem a = ringTag then RingSrc s k (a + 8)
    else RingSrc s k a

/-- The buffers of the `RingWeight` at `a` miss the `k` bytes from `lo`. -/
def RingApart (s : MachineState) (a lo : Word) (k : Nat) : Prop :=
  Apart (vecPtr s a) (24 * (vecLen s a).toNat) lo k ∧
    Apart (vecPtr s (a + 24)) (24 * (vecLen s (a + 24)).toNat) lo k

/-- The buffers of the `StackWeight` at `a` miss the `k` bytes from `lo`. -/
def WeightApart (s : MachineState) (a lo : Word) (k : Nat) : Prop :=
  if s.getMem a = eqTag then Apart (vecPtr s (a + 8)) (24 * (vecLen s (a + 8)).toNat) lo k
  else if s.getMem a = ringTag then RingApart s (a + 8) lo k
  else RingApart s a lo k

/-- The `StackClaim` at `a`. -/
def stackClaimAt (s : MachineState) (a : Word) : StackClaimRust :=
  ⟨stackWeightAt s a, eAt s (a + 64)⟩

/-- The `n` claims from `p`. -/
def claimsAt (s : MachineState) (p : Word) (n : Nat) : List StackClaimRust :=
  (List.range n).map fun i ↦ stackClaimAt s (p + BitVec.ofNat 64 (88 * i))

/-! ## `RingWeight::evaluate`, at `0x8000df24` -/

/-- Its 176-byte frame and `mul`'s stack below it (`try_allocate_in`'s and `memcpy`'s are
smaller, `E::square` uses none). -/
@[rv_addr] def ringEvalStack : Nat := 176 + mulStack

/-- `a0` = the result, `a1` = the `RingWeight`, `a2`/`a3` = `r_prime`. -/
structure RingEvalPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s ringEvalStack
  rodata : RodataOk s
  out : Dst s ringEvalStack (s.getReg .x10) 24
  self : RingSrc s ringEvalStack (s.getReg .x11)
  rPrime : Src s ringEvalStack (s.getReg .x12) (24 * (s.getReg .x13).toNat)
  outSelf : Apart (s.getReg .x10) 24 (s.getReg .x11) 48
  outPoint : Apart (s.getReg .x10) 24 (vecPtr s (s.getReg .x11))
    (24 * (vecLen s (s.getReg .x11)).toNat)
  outCoeffs : Apart (s.getReg .x10) 24 (vecPtr s (s.getReg .x11 + 24))
    (24 * (vecLen s (s.getReg .x11 + 24)).toNat)
  outRPrime : Apart (s.getReg .x10) 24 (s.getReg .x12) (24 * (s.getReg .x13).toNat)

/-- The weight at `r_prime`, which the mirror returns; memory changes only in the result, the
stack, `NEXT` and the heap allocated. -/
structure RingEvalPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : (ringWeightAt s (s.getReg .x11)).evaluate
    (eListAt s (s.getReg .x12) (s.getReg .x13).toNat) = some (eAt t (s.getReg .x10))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s ringEvalStack) ringEvalStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev RingEvalSpec : Prop := FunSpec Image.code 0x8000df24 RingEvalPre RingEvalPost

/-! ## `StackBasis::evaluate`, at `0x8000d0a4` -/

/-- Its 192-byte frame and `RingWeight::evaluate`'s stack below it (the other callees' are
smaller; `dot`, a tail call, runs on the caller's `sp`). -/
@[rv_addr] def basisStack : Nat := 192 + ringEvalStack

/-- The claims slice of the `StackBasis` at `a`. -/
@[rv_addr] def basisClaimsPtr (s : MachineState) (a : Word) : Word := s.getMem (a + 24)
@[rv_addr] def basisClaimsLen (s : MachineState) (a : Word) : Nat := (s.getMem (a + 32)).toNat

/-- `a0` = the result, `a1` = the `StackBasis`, `a2`/`a3` = the point. -/
structure BasisPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s basisStack
  rodata : RodataOk s
  out : Dst s basisStack (s.getReg .x10) 24
  self : Src s basisStack (s.getReg .x11) 40
  scales : Src s basisStack (vecPtr s (s.getReg .x11)) (24 * (vecLen s (s.getReg .x11)).toNat)
  claims : Src s basisStack (basisClaimsPtr s (s.getReg .x11)) (88 * basisClaimsLen s (s.getReg .x11))
  weights : ∀ i < basisClaimsLen s (s.getReg .x11),
    WeightSrc s basisStack (basisClaimsPtr s (s.getReg .x11) + BitVec.ofNat 64 (88 * i))
  point : Src s basisStack (s.getReg .x12) (24 * (s.getReg .x13).toNat)
  outScales : Apart (s.getReg .x10) 24 (vecPtr s (s.getReg .x11))
    (24 * (vecLen s (s.getReg .x11)).toNat)

/-- The batched basis at the point, which the mirror returns; memory changes only in the result,
the stack, `NEXT` and the heap allocated. -/
structure BasisPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : stackBasisEvaluate (claimsAt s (basisClaimsPtr s (s.getReg .x11))
      (basisClaimsLen s (s.getReg .x11))) (vecEs s (s.getReg .x11))
      (eListAt s (s.getReg .x12) (s.getReg .x13).toNat) = some (eAt t (s.getReg .x10))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
    Within a (stackLo s basisStack) basisStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev BasisSpec : Prop := FunSpec Image.code 0x8000d0a4 BasisPre BasisPost

/-! ## `ring_switch`, at `0x80009754` -/

/-- Its 464-byte frame and `poly_eval`'s stack below it (`samples`', `E::pow`'s, `mul`'s and the
allocator's are smaller; `reserve` takes its fast path). -/
@[rv_addr] def ringSwitchStack : Nat := 464 + MultilinearContracts.polyEvalStack

/-- What a function taking the transcript at `p` asks of it, its stack the `k` bytes below `sp`:
the transcript and the proof's bytes it reads in place, apart from the stack, the free heap and
`.rodata`. -/
structure TranscriptIn (s : MachineState) (k : Nat) (p : Word) : Prop where
  ok : TranscriptOk s p
  stack : Apart p transcriptSize (stackLo s k) k
  proofStack : ProofApart s p (stackLo s k) k
  free : Outside s p transcriptSize
  proofFree : Outside s (proofAt s p) 48
  streamFree : Outside s (streamPtr s p) (24 * streamLen s p)
  rodata : Apart p transcriptSize rodataBase Rv64Verifier.rodataSize

/-- `a0` = the result `(E, RingWeight)`: the target at `0`, the weight at `24` (72 bytes); `a1` =
the `point` `Vec`, moved into the weight; `a2`/`a3` = `s`; `a4` = the transcript. -/
structure RingSwitchPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s ringSwitchStack
  rodata : RodataOk s
  out : Dst s ringSwitchStack (s.getReg .x10) 72
  point : Src s ringSwitchStack (s.getReg .x11) 24
  pointBuf : Src s ringSwitchStack (vecPtr s (s.getReg .x11)) (24 * (vecLen s (s.getReg .x11)).toNat)
  slices : Src s ringSwitchStack (s.getReg .x12) (24 * (s.getReg .x13).toNat)
  self : TranscriptIn s ringSwitchStack (s.getReg .x14)
  outSelf : Apart (s.getReg .x10) 72 (s.getReg .x14) transcriptSize
  outProof : ProofApart s (s.getReg .x14) (s.getReg .x10) 72
  outPoint : Apart (s.getReg .x10) 72 (s.getReg .x11) 24
  outPointBuf : Apart (s.getReg .x10) 72 (vecPtr s (s.getReg .x11))
    (24 * (vecLen s (s.getReg .x11)).toNat)
  outSlices : Apart (s.getReg .x10) 72 (s.getReg .x12) (24 * (s.getReg .x13).toNat)
  pointSponge : Apart (s.getReg .x11) 24 (s.getReg .x14 + 8) 344
  pointBufSponge : Apart (vecPtr s (s.getReg .x11)) (24 * (vecLen s (s.getReg .x11)).toNat)
    (s.getReg .x14 + 8) 344
  slicesSponge : Apart (s.getReg .x12) (24 * (s.getReg .x13).toNat) (s.getReg .x14 + 8) 344

/-- What `ringSwitchRust` returns, the transcript then standing for the mirror's: the target, the
`point` `Vec` moved as is, a new `Vec` of the coefficients. Memory changes only in the result, the
sponge and offsets, the stack, `NEXT` and the heap allocated. -/
structure RingSwitchPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x14) T → ∃ r T',
    (ringSwitchRust (vecEs s (s.getReg .x11))
      (eListAt s (s.getReg .x12) (s.getReg .x13).toNat)).run T = some (r, T') ∧
    eAt t (s.getReg .x10) = r.1 ∧ ringWeightAt t (s.getReg .x10 + 24) = r.2 ∧
    t.getMem (s.getReg .x10 + 24) = s.getMem (s.getReg .x11) ∧
    t.getMem (s.getReg .x10 + 32) = s.getMem (s.getReg .x11 + 8) ∧
    t.getMem (s.getReg .x10 + 40) = s.getMem (s.getReg .x11 + 16) ∧
    NewVecE s t (s.getReg .x10 + 48) r.2.coefficients ∧ TranscriptAt t (s.getReg .x14) T'
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 72 ∨ Within a (s.getReg .x14 + 8) 344 ∨
    Within a (stackLo s ringSwitchStack) ringSwitchStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev RingSwitchSpec : Prop := FunSpec Image.code 0x80009754 RingSwitchPre RingSwitchPost

/-! ## `Vec<StackClaim>::extend_desugared` over `walk`'s `on_stack` claims, at `0x80009b94` -/

/-- The `Option<Placement>` at `a` (24 bytes): `Some` when the tag's bit 0 is set, `variables` and
`index` at `8`, `16`. -/
def placementAt (s : MachineState) (a : Word) : Option Model.PlacementRust :=
  if s.getMem a &&& 1 = 0 then none else some ⟨(s.getMem (a + 8)).toNat, s.getMem (a + 16)⟩

def placementsAt (s : MachineState) (p : Word) (n : Nat) : List (Option Model.PlacementRust) :=
  (List.range n).map fun i ↦ placementAt s (p + BitVec.ofNat 64 (24 * i))

/-- The `ColumnClaim` at `a` (56 bytes): `point` at `0`, `column` at `24`, `value` at `32`. -/
def columnClaimAt (s : MachineState) (a : Word) : Model.LayoutMirror.ColumnClaimRust :=
  ⟨(s.getMem (a + 24)).toNat, vecEs s a, eAt s (a + 32)⟩

def columnClaimsAt (s : MachineState) (p : Word) (n : Nat) :
    List Model.LayoutMirror.ColumnClaimRust :=
  (List.range n).map fun i ↦ columnClaimAt s (p + BitVec.ofNat 64 (56 * i))

/-- `ColumnClaim::on_stack` on the layout's placements and stack size, as a `StackClaim`. -/
def onStackAt (placements : List (Option Model.PlacementRust)) (stackLog : ℕ)
    (c : Model.LayoutMirror.ColumnClaimRust) : Option StackClaimRust :=
  match placements.getD c.column none with
  | none => none
  | some p => some ⟨.eq (p.stackPoint c.point stackLog), c.value⟩

/-- It is the walk mirror's `on_stack`. -/
theorem onStackAt_eq (l : Model.LayoutMirror.LayoutRust) (c : Model.LayoutMirror.ColumnClaimRust) :
    onStackAt l.placements l.stackLog c = (c.onStack l).map fun pv ↦ ⟨.eq pv.1, pv.2⟩ := by
  simp only [onStackAt, Model.LayoutMirror.ColumnClaimRust.onStack]
  cases l.placements.getD c.column none <;> rfl

/-- The `Vec<StackClaim>` at `a`'s claims. -/
def stackClaimsAt (s : MachineState) (a : Word) : List StackClaimRust :=
  claimsAt s (vecPtr s a) (vecLen s a).toNat

/-- `<[&[E]] as Concat<E>>::concat`, at `0x8000cfc4`: its stack, its callees' included. -/
@[rv_addr] def sliceConcatStack : Nat := 64 + Runtime.reserveStack

/-- Its 240-byte frame and the deepest callee's stack below it. -/
@[rv_addr] def extendStack : Nat := 240 + max sliceConcatStack (max MultilinearContracts.selectorStack Runtime.growStack)

/-- The iterator at `a1`: the current claim, the end, the `Layout`. -/
@[rv_addr] def itCur (s : MachineState) : Word := s.getMem (s.getReg .x11)
@[rv_addr] def itEnd (s : MachineState) : Word := s.getMem (s.getReg .x11 + 8)
@[rv_addr] def itLayout (s : MachineState) : Word := s.getMem (s.getReg .x11 + 16)
/-- The claims left, the layout's placements and `stack_log`. -/
@[rv_addr] def itCount (s : MachineState) : Nat := ((itEnd s).toNat - (itCur s).toNat) / 56
@[rv_addr] def placementsPtr (s : MachineState) : Word := s.getMem (itLayout s + 104)
@[rv_addr] def placementsLen (s : MachineState) : Nat := (s.getMem (itLayout s + 112)).toNat
@[rv_addr] def stackLogAt (s : MachineState) : Nat := (s.getMem (itLayout s + 184)).toNat

/-- The `n` bytes from `a` miss the `Vec` at `a0` and the iterator at `a1`. -/
def ExtendOff (s : MachineState) (a : Word) (n : Nat) : Prop :=
  Apart a n (s.getReg .x10) 24 ∧ Apart a n (s.getReg .x11) 24

/-- `a0` = the `Vec<StackClaim>`, `a1` = the iterator; every placement within the stack. -/
structure ExtendPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s extendStack
  rodata : RodataOk s
  self : Dst s extendStack (s.getReg .x10) 24
  vec : VecOk s (s.getReg .x10) 88 8
  iter : Dst s extendStack (s.getReg .x11) 24
  bounds : (itCur s).toNat ≤ (itEnd s).toNat ∧ ((itEnd s).toNat - (itCur s).toNat) % 56 = 0
  claims : Src s extendStack (itCur s) (56 * itCount s)
  points : ∀ i < itCount s, Src s extendStack
    (vecPtr s (itCur s + BitVec.ofNat 64 (56 * i)))
    (24 * (vecLen s (itCur s + BitVec.ofNat 64 (56 * i))).toNat)
  layout : Src s extendStack (itLayout s) 192
  placements : Src s extendStack (placementsPtr s) (24 * placementsLen s)
  within : ∀ p ∈ placementsAt s (placementsPtr s) (placementsLen s), ∀ q, p = some q →
    q.variableCount ≤ stackLogAt s
  selfIter : Apart (s.getReg .x10) 24 (s.getReg .x11) 24
  /-- The `Vec` full (as `vec![claim]` leaves it), so a push moves it to a new buffer. -/
  full : vecLen s (s.getReg .x10) = vecCap s (s.getReg .x10)
  elems : Src s extendStack (vecPtr s (s.getReg .x10)) (88 * (vecLen s (s.getReg .x10)).toNat)
  weights : ∀ i < (vecLen s (s.getReg .x10)).toNat,
    WeightSrc s extendStack (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i))
  /-- What it reads misses the `Vec` and the iterator, which it writes. -/
  elemsOff : ExtendOff s (vecPtr s (s.getReg .x10)) (88 * (vecLen s (s.getReg .x10)).toNat)
  weightsOff : ∀ i < (vecLen s (s.getReg .x10)).toNat,
    WeightApart s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) (s.getReg .x10) 24 ∧
      WeightApart s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) (s.getReg .x11) 24
  claimsOff : ExtendOff s (itCur s) (56 * itCount s)
  pointsOff : ∀ i < itCount s, ExtendOff s (vecPtr s (itCur s + BitVec.ofNat 64 (56 * i)))
    (24 * (vecLen s (itCur s + BitVec.ofNat 64 (56 * i))).toNat)
  layoutOff : ExtendOff s (itLayout s) 192
  placementsOff : ExtendOff s (placementsPtr s) (24 * placementsLen s)

/-- The claims on the stack appended, the iterator at its end; memory changes only in the `Vec`,
the iterator's position, the stack, `NEXT` and the heap allocated. -/
structure ExtendPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 88 8
  value : stackClaimsAt t (s.getReg .x10) = stackClaimsAt s (s.getReg .x10) ++
    (columnClaimsAt s (itCur s) (itCount s)).filterMap
      (onStackAt (placementsAt s (placementsPtr s) (placementsLen s)) (stackLogAt s))
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨ Within a (s.getReg .x11) 8 ∨
    Within a (stackLo s extendStack) extendStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev ExtendSpec : Prop := FunSpec Image.code 0x80009b94 ExtendPre ExtendPost

/-! ## `verify_stacked_opening`, at `0x80009db8`

`verify_whir` and the Merkle checks inlined. `Ok(())` is `a0 = -1` (the caller's check at
`0x8000412c`); an `Err` is its discriminant. What the function reads lies apart from what it
writes: the sponge and both offsets, `352` bytes from the transcript's `8`. -/

@[rv_addr] def okTag : Word := 0xffffffffffffffff

/-- The root at `a`: four little-endian lanes. -/
def digestAt (s : MachineState) (a : Word) : LeanVM.Protocol.Digest :=
  Vector.ofFn fun i : Fin 4 ↦ UInt64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * i.val)))

/-- Its 1040-byte frame and the deepest callee's stack below it, `StackBasis::evaluate`'s
(`sumcheck_round_poly`'s, `keccak_hash`'s and the rest are smaller). -/
@[rv_addr] def vsoStack : Nat := 1040 + max basisStack Transcript.roundPolyStack

/-- `a0` = the transcript, `a1` = the root (32 bytes), `a2` = `stack_log`, `a3` =
`log_inv_rate`, `a4`/`a5` = the claims. -/
structure VsoPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s vsoStack
  rodata : RodataOk s
  self : TranscriptIn s vsoStack (s.getReg .x10)
  root : Src s vsoStack (s.getReg .x11) 32
  claims : Src s vsoStack (s.getReg .x14) (88 * (s.getReg .x15).toNat)
  weights : ∀ i < (s.getReg .x15).toNat,
    WeightSrc s vsoStack (s.getReg .x14 + BitVec.ofNat 64 (88 * i))
  rootSponge : Apart (s.getReg .x11) 32 (s.getReg .x10 + 8) 352
  claimsSponge : Apart (s.getReg .x14) (88 * (s.getReg .x15).toNat) (s.getReg .x10 + 8) 352
  weightsSponge : ∀ i < (s.getReg .x15).toNat,
    WeightApart s (s.getReg .x14 + BitVec.ofNat 64 (88 * i)) (s.getReg .x10 + 8) 352
  proofSponge : ProofApart s (s.getReg .x10) (s.getReg .x10 + 8) 352
  /-- A checked transcript (`true`, as the grinding check reads its low bit): a replay skips the
  checks, and its `Ok` says nothing. -/
  checked : byteAt s (s.getReg .x10 + 360) = 1
  /-- The root, which the function overwrites with each level's commitment, misses what it reads
  besides. -/
  rootSelf : Apart (s.getReg .x11) 32 (s.getReg .x10) transcriptSize
  rootRodata : Apart (s.getReg .x11) 32 rodataBase Rv64Verifier.rodataSize
  rootProof : ProofApart s (s.getReg .x10) (s.getReg .x11) 32
  rootClaims : Apart (s.getReg .x11) 32 (s.getReg .x14) (88 * (s.getReg .x15).toNat)
  rootWeights : ∀ i < (s.getReg .x15).toNat,
    WeightApart s (s.getReg .x14 + BitVec.ofNat 64 (88 * i)) (s.getReg .x11) 32

/-- `Ok` only when `verifyStackedOpeningRust` returns, on a transcript whose roots so far are the
stack's alone, at the shape level `0` opens, and whose Merkle openings `OpeningsAt` places in
memory: the transcript then stands for the mirror's. Memory changes only in the sponge and offsets,
the root (the last level's commitment overwrites it), the stack, `NEXT` and the heap allocated. -/
structure VsoPost (OpeningsAt : MachineState → Word → Model.TState → Prop) (s t : MachineState) :
    Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : t.getReg .x10 = okTag → ∀ T, TranscriptAt s (s.getReg .x10) T →
    OpeningsAt s (s.getReg .x10) T →
    T.roots = [(digestAt s (s.getReg .x11), Model.stackShape (s.getReg .x12).toNat
      (s.getReg .x13).toNat)] →
    ∃ T', (verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
      (claimsAt s (s.getReg .x14) (s.getReg .x15).toNat)).run T = some ((), T') ∧
      TranscriptAt t (s.getReg .x10) T'
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10 + 8) 352 ∨ Within a (s.getReg .x11) 32 ∨
    Within a (stackLo s vsoStack) vsoStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev VsoSpec (OpeningsAt : MachineState → Word → Model.TState → Prop) : Prop :=
  FunSpec Image.code 0x80009db8 VsoPre (VsoPost OpeningsAt)

end Rv64Verifier.PcsContracts
