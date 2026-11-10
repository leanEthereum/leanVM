import Rv64Verifier.Proofs.Main.Contracts
import Rv64Verifier.Proofs.End
import Rv64Verifier.Proofs.Runtime.Alloc

/-!
# `main` in stages

`main` (at `0x800002cc`, `Blocks/F3.lean`) runs in four stages, each a `Runs` from one state of
`main` to the next (or to a dead end), all keeping `MInv`: `main`'s frame at `msp` with the
caller's registers saved in it, the input words in place, the heap in shape, `.rodata` in place.

* `IvStage`: the prologue, the table's length, and `Bytecode::new`'s IV (`keccak_hash` of `TAG` and
  the table's bytes), up to `0x80000404` (`AfterIv`).
* `NewStage`: `Bytecode::new`'s grouping, up to `0x80000a20`, its four `Vec`s holding `newRust`'s
  (`AfterNew`).
* `ParseStage`: the `Bytecode` assembled, the public input, the stream and the openings read, up to
  the call of `walk` (`AtWalk`): what they hold is `decodeInput`'s.
* `walk` and the epilogue (`Proofs/Main/All.lean`).

The input lies from `inputBase` and the heap from `0x20000000`: an input of more than
`inputWords` words overlaps the heap, whose allocations then overwrite words before `main` reads
them, so `main` is specified for inputs that fit.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End

/-- `main`'s `sp`: `_start`'s, less the 576-byte frame. -/
@[rv_addr] def msp : Word := 0xbffffdb0

/-- The input words that fit below the heap. -/
@[rv_addr] def inputWords : Nat := 2 ^ 25

/-- Where the prologue saves the caller's registers, from `msp`. -/
def mainSlots : List (Nat × Reg) :=
  [(472, .x27), (480, .x26), (488, .x25), (496, .x24), (504, .x23), (512, .x22), (520, .x21),
    (528, .x20), (536, .x19), (544, .x18), (552, .x9), (560, .x8), (568, .x1)]

/-- Inside `main`, entered at `s` on the input `words`. -/
structure MInv (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  fits : words.length ≤ inputWords
  sp : u.getReg .x2 = msp
  slots : ∀ p ∈ mainSlots, u.getMem (msp + BitVec.ofNat 64 p.1) = s.getReg p.2
  input : ∀ i (h : i < words.length), u.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i]
  heap : HeapOk u
  rodata : RodataOk u

/-- From every state satisfying `P`, the image reaches one satisfying `Q`, or a dead end. -/
def Runs (P Q : MachineState → Prop) : Prop :=
  ∀ u, P u → ∃ v, Reaches Image.code u v ∧ (Q v ∨ Dead Image.code v)

theorem Runs.trans {P Q R : MachineState → Prop} (h₁ : Runs P Q) (h₂ : Runs Q R) : Runs P R := by
  intro u hu
  obtain ⟨v, huv, hv | hv⟩ := h₁ u hu
  · obtain ⟨w, hvw, hw⟩ := h₂ v hv
    exact ⟨w, huv.trans hvw, hw⟩
  · exact ⟨v, huv, Or.inr hv⟩

theorem Runs.mono {P P' Q Q' : MachineState → Prop} (h : Runs P Q) (hP : ∀ u, P' u → P u)
    (hQ : ∀ u, Q u → Q' u) : Runs P' Q' := by
  intro u hu
  obtain ⟨v, huv, hv⟩ := h u (hP u hu)
  exact ⟨v, huv, hv.imp_left (hQ v)⟩

/-- The table: the words after the first, as many as the first says. -/
def tbl (words : List Word) : List Word := (words.drop 1).take (words.getD 0 0).toNat

/-- After `keccak_hash` (`0x80000404`): `s3` is the table's length, the input slice (`msp + 88`,
`msp + 96`) past the table, the IV at `msp + 320`. -/
structure AfterIv (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x80000404
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  n : u.getReg .x19 = words.getD 0 0
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 1))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 1)
  iv : bytesAt u (msp + 320) 32 = Model.fiatShamirIvRust (tbl words)

/-- The `Vec`s `Bytecode::new` builds hold `bc`'s `blocks`, `words`, `positions` and `bytes`, at
`msp + 400`, `424`, `448` and `240`, in allocated buffers, their pointers below `NEXT`. -/
structure NewVecs (u : MachineState) (bc : Model.BytecodeRust) : Prop where
  blocks : blocksAt u (vecPtr u (msp + 400)) (vecLen u (msp + 400)).toNat = bc.blocks
  words : wordsAt u (vecPtr u (msp + 424)) (vecLen u (msp + 424)).toNat = bc.words
  positions : halvesAt u (vecPtr u (msp + 448)) (vecLen u (msp + 448)).toNat = bc.positions
  bytes : halvesAt u (vecPtr u (msp + 240)) (vecLen u (msp + 240)).toNat = bc.bytes
  blocksBuf : Buf u (vecPtr u (msp + 400)) (24 * (vecLen u (msp + 400)).toNat) 8
  wordsBuf : Buf u (vecPtr u (msp + 424)) (16 * (vecLen u (msp + 424)).toNat) 8
  positionsBuf : Buf u (vecPtr u (msp + 448)) (2 * (vecLen u (msp + 448)).toNat) 2
  bytesBuf : Buf u (vecPtr u (msp + 240)) (2 * (vecLen u (msp + 240)).toNat) 2
  blocksLe : (vecPtr u (msp + 400)).toNat ≤ heapNext u
  wordsLe : (vecPtr u (msp + 424)).toNat ≤ heapNext u
  positionsLe : (vecPtr u (msp + 448)).toNat ≤ heapNext u
  bytesLe : (vecPtr u (msp + 240)).toNat ≤ heapNext u

/-- After `Bytecode::new`'s loop (`0x80000a20`): as `AfterIv`, the table's length at `msp`, and
the four `Vec`s holding `newRust`'s. -/
structure AfterNew (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x80000a20
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  n : u.getMem msp = words.getD 0 0
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 1))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 1)
  iv : bytesAt u (msp + 320) 32 = Model.fiatShamirIvRust (tbl words)
  vecs : ∃ bc, Model.newRust (tbl words) = some bc ∧ NewVecs u bc

/-- At `walk`'s entry, called from `0x80000dc4`: its arguments in place, holding what
`decodeInput` reads. -/
structure AtWalk (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x80000ef8
  ra : u.getReg .x1 = 0x80000dc8
  a0 : u.getReg .x10 = msp + 320
  pre : WalkCallPre u
  ghost : ∃ table publicInput proof, decodeInput words = some (table, publicInput, proof) ∧
    table.length < 2 ^ 64 ∧
    Model.newRust (table.map BF64.toBitVec) = some (readBytecode u (u.getReg .x11)) ∧
    bytesAt u (u.getReg .x12) 32 = Model.byteBits (KeccakHash.digestBytes publicInput) ∧
    readProof u (u.getReg .x13) = proof

/-- The prologue and the IV. -/
def IvStage : Prop := ∀ s words, s.pc = mainEntry → MainPre words s → words.length ≤ inputWords →
  ∃ v, Reaches Image.code s v ∧ (AfterIv s words v ∨ Dead Image.code v)

/-- `Bytecode::new`'s grouping. -/
def NewStage : Prop := ∀ s words, Runs (AfterIv s words) (AfterNew s words)

/-- The `Bytecode`, the public input and the `Proof`, up to the call of `walk`. -/
def ParseStage : Prop := ∀ s words, Runs (AfterNew s words) (AtWalk s words)

end Rv64Verifier.Proofs.Main
