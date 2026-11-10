import Rv64Verifier.Proofs.Bytecode.Contracts
import Rv64Verifier.Proofs.Gkr.Contracts
import Rv64Verifier.Model.Walk
import Rv64Verifier.Proofs.Layout.Repr

/-!
# The contract of `walk`, at `0x80000ef8`

`verify_execution` is `walk(bytecode, public_input, proof, true)`, inlined into its one caller,
`main`; `checked` is the constant `true`. `a0` = the `Result<Summary, VerifierError>` (80 bytes;
`Err` is `errNiche` in its first word, the capacity of `Summary::table_rows`, and `main` reads
only that word), `a1` = the `Bytecode` (`readBytecode`), `a2` = the 32 bytes of the public input
(read a byte at a time), `a3` = the `Proof`: its stream (`Vec<E>`) at `+0`, its Merkle openings
(`Vec<Vec<MerklePath>>`) at `+24`.

The openings' representation is `OpeningsIn`, a parameter: what `verify_stacked_opening`'s
`OpeningsAt` reads, which `walk` passes on (`ProofIn`). Everything `walk` reads lies apart from
what it writes (`ReadOnly`): the result, its stack, `NEXT` and the heap it allocates.

Soundness only: `Ok` (a first word other than `errNiche`) only when `verifyExecutionRust` returns
on the proof the memory holds.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Transcript
  Rv64Verifier.Model

/-- The 2656-byte frame and the deepest callee's stack below it, `verify_keccak`'s. -/
@[rv_addr] def walkStack : Nat := 2656 + Gkr.verifyKeccakStack

/-- The `n` bytes from `a` are only read: they miss the free heap and `NEXT`, the stack, the result
and `.rodata`. -/
@[rv_addr] def ReadOnly (s : MachineState) (a : Word) (n : Nat) : Prop :=
  Outside s a n ∧ Apart a n (stackLo s walkStack) walkStack ∧ Apart a n (s.getReg .x10) 80 ∧
    Apart a n rodataBase rodataSize

/-- The `Bytecode` at `p`, mapped, and every part of it only read. -/
structure BytecodeIn (s : MachineState) (p : Word) : Prop where
  mem : Proofs.Bytecode.BytecodeMem s p
  self : ReadOnly s p 136
  blocks : ReadOnly s (vecPtr s p) (24 * (vecLen s p).toNat)
  words : ReadOnly s (vecPtr s (p + 24)) (16 * (vecLen s (p + 24)).toNat)
  positions : ReadOnly s (vecPtr s (p + 48)) (2 * (vecLen s (p + 48)).toNat)
  bytes : ReadOnly s (vecPtr s (p + 72)) (2 * (vecLen s (p + 72)).toNat)

/-- The `Proof` at `a` holds `proof`: its stream, and its openings as `OpeningsIn` places them. -/
structure ProofIn (OpeningsIn : MachineState → Word → List (List Opening) → Prop)
    (s : MachineState) (a : Word) (proof : Proof) : Prop where
  stream : eListAt s (vecPtr s a) (vecLen s a).toNat = proof.stream
  openingsLen : (vecLen s (a + 24)).toNat = proof.openings.length
  openings : OpeningsIn s a proof.openings

structure WalkPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s walkStack
  rodata : RodataOk s
  out : Region (s.getReg .x10) 80
  outFree : Outside s (s.getReg .x10) 80
  outStack : Apart (s.getReg .x10) 80 (stackLo s walkStack) walkStack
  outRodata : Apart (s.getReg .x10) 80 rodataBase rodataSize
  bytecode : BytecodeIn s (s.getReg .x11)
  input : Region (s.getReg .x12) 32
  inputRO : ReadOnly s (s.getReg .x12) 32
  proof : Region (s.getReg .x13) 48
  proofRO : ReadOnly s (s.getReg .x13) 48
  stream : (vecLen s (s.getReg .x13)).toNat = 0 ∨
    Region (vecPtr s (s.getReg .x13)) (24 * (vecLen s (s.getReg .x13)).toNat)
  streamRO : ReadOnly s (vecPtr s (s.getReg .x13)) (24 * (vecLen s (s.getReg .x13)).toNat)

/-- What `walk` may write: the result, its stack, `NEXT` and the heap it allocates. -/
@[rv_addr] def WalkW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 80 ∨ Within a (stackLo s walkStack) walkStack ∨ Within a nextAddr 8 ∨
    Fresh s t a

/-- `Ok` only when `verifyExecutionRust` returns on the `Bytecode`, the public input's bytes and
every proof the memory holds. Memory is kept doubleword by doubleword, for the doublewords that do
not wrap past `2 ^ 64` (`Layout.DFrame`, what the layout functions' contracts give). -/
structure WalkPost (OpeningsIn : MachineState → Word → List (List Opening) → Prop)
    (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : t.getMem (s.getReg .x10) ≠ errNiche → ∀ proof, ProofIn OpeningsIn s (s.getReg .x13) proof →
    ∃ summary, verifyExecutionRust (Proofs.Bytecode.readBytecode s (s.getReg .x11))
      (bytesAt s (s.getReg .x12) 32) proof = some summary
  frame : Rv64Verifier.Layout.DFrame s t (WalkW s t)

abbrev WalkSpec (OpeningsIn : MachineState → Word → List (List Opening) → Prop) : Prop :=
  FunSpec Image.code 0x80000ef8 WalkPre (WalkPost OpeningsIn)

end Rv64Verifier.Proofs.Walk
