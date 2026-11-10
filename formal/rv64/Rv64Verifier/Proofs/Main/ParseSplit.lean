import Rv64Verifier.Proofs.Main.Decode

/-!
# `ParseStage` in two

`ParseHead`: from `AfterNew`, `0x80000a20` assembles the `Bytecode` at `msp + 104` (the four
`Vec`s, the length at `msp + 200`, the IV copied to `msp + 208`), and `Input::digest` reads the
public input into `msp + 240` (`ParseA`, at `0x80000aac`). `ParseRest`: the stream, the openings,
the check that nothing is left over, and the call of `walk` (`AtWalk`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode

/-- The `Bytecode` at `msp + 104`'s buffers are allocated, their pointers below `NEXT`. -/
structure BcBufs (u : MachineState) : Prop where
  blocks : Buf u (vecPtr u (msp + 104)) (24 * (vecLen u (msp + 104)).toNat) 8
  words : Buf u (vecPtr u (msp + 128)) (16 * (vecLen u (msp + 128)).toNat) 8
  positions : Buf u (vecPtr u (msp + 152)) (2 * (vecLen u (msp + 152)).toNat) 2
  bytes : Buf u (vecPtr u (msp + 176)) (2 * (vecLen u (msp + 176)).toNat) 2
  blocksLe : (vecPtr u (msp + 104)).toNat ≤ heapNext u
  wordsLe : (vecPtr u (msp + 128)).toNat ≤ heapNext u
  positionsLe : (vecPtr u (msp + 152)).toNat ≤ heapNext u
  bytesLe : (vecPtr u (msp + 176)).toNat ≤ heapNext u

/-- After the public input (`0x80000aac`): `n + 5` words read, the `Bytecode` at `msp + 104` is
`newRust`'s, the public input's bytes at `msp + 240`. -/
structure ParseA (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x80000aac
  len : (words.getD 0 0).toNat + 5 ≤ words.length
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 5))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 5)
  bc : Model.newRust (tbl words) = some (readBytecode u (msp + 104))
  bufs : BcBufs u
  pi : bytesAt u (msp + 240) 32 =
    ((words.drop ((words.getD 0 0).toNat + 1)).take 4).flatMap Model.toLeBytes

/-- The `Bytecode`, its IV and the public input. -/
def ParseHead : Prop := ∀ s words, Runs (AfterNew s words) (ParseA s words)

/-- The stream, the openings, and the call of `walk`. -/
def ParseRest : Prop := ∀ s words, Runs (ParseA s words) (AtWalk s words)

theorem parse_stage_of (hH : ParseHead) (hR : ParseRest) : ParseStage :=
  fun s words ↦ (hH s words).trans (hR s words)

end Rv64Verifier.Proofs.Main
