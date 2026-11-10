import Rv64Verifier.Proofs.Bytecode.Contracts
import Rv64Verifier.Proofs.Rodata
import Rv64Verifier.Model.Walk
import Rv64Verifier.EndStatement

/-!
# What `main` needs of `walk`

`main` (`guest/src/main.rs`) calls `verify_execution`, which LTO inlines down to a call of `walk`
at `0x80000ef8` with `checked` constant: `a0` = where the `Result<Summary, VerifierError>` goes
(80 bytes), `a1` = the `Bytecode` (`readBytecode`), `a2` = the 32 bytes of the public input,
`a3` = the `Proof`. `main` accepts when the result's first doubleword is not `-1`, the `Err` niche.

The `Proof` as the image lays it out (`readProof`): `stream: Vec<E>` at `0`,
`merkle_openings: Vec<Vec<MerklePath>>` at `24`; a `MerklePath` is 56 bytes, `leaf: Vec<K>` at `0`,
`siblings: Vec<[u8; 32]>` at `24`, `leaf_index` at `48`. A sibling is read as bytes: its buffer is
aligned to one byte only.

`WalkCallSpec`: given the parts mapped, aligned, allocated and apart from `walk`'s stack and its
result (`WalkCallPre`), `walk` returns `Ok` only if `verifyExecutionRust` of what they hold does, and
writes only its result, its stack, `NEXT` and memory it allocates.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode

/-! ## The `Proof` in memory -/

/-- A digest from its 32 bytes, little-endian words. -/
def digestOfBytes (bytes : List (BitVec 8)) : Digest :=
  Vector.ofFn fun i : Fin 4 ↦ UInt64.ofBitVec ((Model.digestWordsRust bytes).getD i.val 0)

/-- The `MerklePath` at `a`. -/
def pathAt (s : MachineState) (a : Word) : Opening where
  leafIndex := (s.getMem (a + 48)).toNat
  leaf := (vecWords s a).map BF64.ofBitVec
  path := (List.range (vecLen s (a + 24)).toNat).map fun k ↦
    digestOfBytes (bytesAt s (vecPtr s (a + 24) + BitVec.ofNat 64 (32 * k)) 32)

/-- The `Vec<MerklePath>` at `a`. -/
def phaseAt (s : MachineState) (a : Word) : List Opening :=
  (List.range (vecLen s a).toNat).map fun j ↦ pathAt s (vecPtr s a + BitVec.ofNat 64 (56 * j))

/-- The `Proof` at `p`. -/
def readProof (s : MachineState) (p : Word) : Proof where
  stream := vecEs s p
  openings := (List.range (vecLen s (p + 24)).toNat).map fun i ↦
    phaseAt s (vecPtr s (p + 24) + BitVec.ofNat 64 (24 * i))

/-! ## Where `walk`'s arguments lie -/

/-- `walk`'s frame is `2656` bytes; its callees' below it are bounded by this. -/
@[rv_addr] def walkStack : Nat := 0x1000000

/-- The `Result<Summary, VerifierError>`. -/
@[rv_addr] def walkOutSize : Nat := 80

/-- `Err`'s niche in the result's first doubleword. -/
@[rv_addr] def errTag : Word := 0xffffffffffffffff

/-- The `n` bytes from `a`, aligned to `al`, are mapped, allocated, and apart from `walk`'s stack
and its result at `out`; none when `n = 0`. -/
@[rv_addr] def Part (s : MachineState) (out a : Word) (n al : Nat) : Prop :=
  n = 0 ∨ (Runtime.Mapped a n ∧ a.toNat % al = 0 ∧ Outside s a n ∧
    Apart a n (stackLo s walkStack) walkStack ∧ Apart a n out walkOutSize)

/-- The `Bytecode` at `p` and its four buffers. -/
structure BcMem (s : MachineState) (out p : Word) : Prop where
  self : Part s out p 136 8
  blocks : Part s out (vecPtr s p) (24 * (vecLen s p).toNat) 8
  words : Part s out (vecPtr s (p + 24)) (16 * (vecLen s (p + 24)).toNat) 8
  positions : Part s out (vecPtr s (p + 48)) (2 * (vecLen s (p + 48)).toNat) 2
  bytes : Part s out (vecPtr s (p + 72)) (2 * (vecLen s (p + 72)).toNat) 2

/-- The `MerklePath` at `a`'s two buffers. -/
structure PathMem (s : MachineState) (out a : Word) : Prop where
  leaf : Part s out (vecPtr s a) (8 * (vecLen s a).toNat) 8
  siblings : Part s out (vecPtr s (a + 24)) (32 * (vecLen s (a + 24)).toNat) 1

/-- The `Vec<MerklePath>` at `a`: its buffer and its paths'. -/
structure PhaseMem (s : MachineState) (out a : Word) : Prop where
  buf : Part s out (vecPtr s a) (56 * (vecLen s a).toNat) 8
  paths : ∀ j < (vecLen s a).toNat, PathMem s out (vecPtr s a + BitVec.ofNat 64 (56 * j))

/-- The `Proof` at `p` and every buffer it reaches. -/
structure ProofMem (s : MachineState) (out p : Word) : Prop where
  self : Part s out p 48 8
  stream : Part s out (vecPtr s p) (24 * (vecLen s p).toNat) 8
  openings : Part s out (vecPtr s (p + 24)) (24 * (vecLen s (p + 24)).toNat) 8
  phases : ∀ i < (vecLen s (p + 24)).toNat,
    PhaseMem s out (vecPtr s (p + 24) + BitVec.ofNat 64 (24 * i))

/-! ## `walk`, at `0x80000ef8` -/

/-- `a0` = the result, `a1` = the `Bytecode`, `a2` = the public input, `a3` = the `Proof`; the heap
in shape, the stack above it, `.rodata` in place. -/
structure WalkCallPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s walkStack
  rodata : RodataOk s
  out : Runtime.Mapped (s.getReg .x10) walkOutSize ∧ (s.getReg .x10).toNat % 8 = 0 ∧
    Outside s (s.getReg .x10) walkOutSize ∧
    Apart (s.getReg .x10) walkOutSize (stackLo s walkStack) walkStack
  bc : BcMem s (s.getReg .x10) (s.getReg .x11)
  publicInput : Part s (s.getReg .x10) (s.getReg .x12) 32 8
  proof : ProofMem s (s.getReg .x10) (s.getReg .x13)

/-- `Ok` only if `verifyExecutionRust` accepts what the arguments hold; memory changes only in the
result, the stack, `NEXT` and what is allocated. -/
structure WalkCallPost (s t : MachineState) : Prop where
  heap : HeapOk t
  ok : t.getMem (s.getReg .x10) ≠ errTag → ∃ summary,
    Model.verifyExecutionRust (readBytecode s (s.getReg .x11)) (bytesAt s (s.getReg .x12) 32)
      (readProof s (s.getReg .x13)) = some summary
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) walkOutSize ∨
    Within a (stackLo s walkStack) walkStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev WalkCallSpec : Prop := FunSpec Image.code 0x80000ef8 WalkCallPre WalkCallPost

end Rv64Verifier.Proofs.Main
