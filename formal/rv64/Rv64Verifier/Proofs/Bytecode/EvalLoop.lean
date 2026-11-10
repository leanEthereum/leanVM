import Rv64Verifier.Proofs.Bytecode.EvalRead
import Rv64Verifier.Proofs.Bytecode.EvalModel
import Rv64Verifier.Proofs.Bytecode.EvalExit

/-!
# `Bytecode::evaluate`: the loop's invariants

The loop over the blocks (`0x80011090`) keeps `Outer e t i`: the first `i` blocks done, the state
`Env.st e i` of `evaluateRust`'s fold in registers (`a2`, `s3`, `a1`, the total in `t0`, `a7`,
`a6`) and the buckets in memory. A block's words (`0x800110d0`) keep `WInv`, the positions of one
word (`0x80011114`) `SInv`; after the words, `Mid`.

The `Bytecode`'s parts as `readBytecode` reads them: `bc_blocks`, `bc_words`, `bc_positions`,
`bc_bytes`.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts Rv64Verifier.Model

/-! ## The `Bytecode` as read -/

namespace Env

/-- `evaluateRust`'s state after the first `i` blocks. -/
def st (e : Env) (i : Nat) : EvalState := evalAfter e.bc e.lowW e.highW i

/-- Block `i`'s words, folded from its start, after `k` of them. -/
def wf (e : Env) (i k : Nat) : List E × Nat :=
  ((e.bc.words.drop (e.st i).wordsStart).take k).foldl (wordStepRust e.lowW e.bc.positions)
    ((e.st i).buckets, (e.st i).positionsStart)

end Env

theorem bc_blocks_length (e : Env) : e.bc.blocks.length = e.blocksLen.toNat := by
  simp [Env.bc, readBytecode, blocksAt, Env.blocksLen, Env.bcp]

theorem bc_words_length (e : Env) : e.bc.words.length = e.wordsLen.toNat := by
  simp [Env.bc, readBytecode, wordsAt, Env.wordsLen, Env.bcp]

theorem bc_positions_length (e : Env) : e.bc.positions.length = e.posLen.toNat := by
  simp [Env.bc, readBytecode, halvesAt, Env.posLen, Env.bcp]

theorem bc_bytes_length (e : Env) : e.bc.bytes.length = e.bytesLen.toNat := by
  simp [Env.bc, readBytecode, halvesAt, Env.bytesLen, Env.bcp]

/-! A buffer read at an index below its length is nonempty, so `BytecodeMem` maps it. -/

theorem EnvOk.blocksMem {e : Env} (he : EnvOk e) {i : Nat} (hi : i < e.bc.blocks.length) :
    Mapped (vecPtr e.s (e.s.getReg .x11)) (24 * (vecLen e.s (e.s.getReg .x11)).toNat) :=
  he.pre.bc.blocks.resolve_left (by
    have := bc_blocks_length e; simp only [Env.blocksLen, Env.bcp] at this; omega)

theorem EnvOk.wordsMem {e : Env} (he : EnvOk e) {j : Nat} (hj : j < e.bc.words.length) :
    Mapped (vecPtr e.s (e.s.getReg .x11 + 24)) (16 * (vecLen e.s (e.s.getReg .x11 + 24)).toNat) :=
  he.pre.bc.words.resolve_left (by
    have := bc_words_length e; simp only [Env.wordsLen, Env.bcp] at this; omega)

theorem EnvOk.positionsMem {e : Env} (he : EnvOk e) {p : Nat} (hp : p < e.bc.positions.length) :
    Mapped (vecPtr e.s (e.s.getReg .x11 + 48)) (2 * (vecLen e.s (e.s.getReg .x11 + 48)).toNat) :=
  he.pre.bc.positions.resolve_left (by
    have := bc_positions_length e; simp only [Env.posLen, Env.bcp] at this; omega)

theorem EnvOk.bytesMem {e : Env} (he : EnvOk e) {b : Nat} (hb : b < e.bc.bytes.length) :
    Mapped (vecPtr e.s (e.s.getReg .x11 + 72)) (2 * (vecLen e.s (e.s.getReg .x11 + 72)).toNat) :=
  he.pre.bc.bytes.resolve_left (by
    have := bc_bytes_length e; simp only [Env.bytesLen, Env.bcp] at this; omega)

theorem bc_blocks (e : Env) {i : Nat} (hi : i < e.bc.blocks.length) :
    e.bc.blocks[i] = ⟨(e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i))).toNat,
      (e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8)).toNat,
      (e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16)).toNat⟩ := by
  simp [Env.bc, readBytecode, blocksAt, Env.blocksPtr, Env.bcp]

theorem bc_words (e : Env) {j : Nat} (hj : j < e.bc.words.length) :
    e.bc.words[j] = (e.s.getMem (e.wordsPtr + BitVec.ofNat 64 (16 * j)),
      (e.s.getMem (e.wordsPtr + BitVec.ofNat 64 (16 * j) + 8)).toNat) := by
  simp [Env.bc, readBytecode, wordsAt, Env.wordsPtr, Env.bcp]

theorem bc_positions (e : Env) {p : Nat} (hp : p < e.bc.positions.length) :
    e.bc.positions[p] = e.s.getHalfword (e.posPtr + BitVec.ofNat 64 (2 * p)) := by
  simp [Env.bc, readBytecode, halvesAt, Env.posPtr, Env.bcp]

theorem bc_bytes (e : Env) {b : Nat} (hb : b < e.bc.bytes.length) :
    e.bc.bytes[b] = e.s.getHalfword (e.bytesPtr + BitVec.ofNat 64 (2 * b)) := by
  simp [Env.bc, readBytecode, halvesAt, Env.bytesPtr, Env.bcp]

/-- The buckets where their doublewords are unchanged. -/
theorem buckets_congr {e : Env} (he : EnvOk e) {t t' : MachineState}
    (h : ∀ a, Within a e.bk 49152 → t'.getMem a = t.getMem a) :
    eListAt t' e.bk 2048 = eListAt t e.bk 2048 := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hb hh
  exact eListAt_congr fun i hi j hj ↦ h _ (by addr_omega [hi, hj, hb, hh])

/-! ## The invariants -/

/-- The registers the loop keeps, and the memory. -/
structure Regs (e : Env) (t : MachineState) : Prop where
  sp : t.getReg .x2 = fp e.s
  mem : LoopMem e t
  x9 : t.getReg .x9 = e.low
  x18 : (t.getReg .x18).toNat = 2 ^ e.m
  x20 : t.getReg .x20 = e.bk
  x21 : t.getReg .x21 = 2048
  x23 : t.getReg .x23 = e.s.getReg .x2 - 136

/-- At the loop's head, before block `i`. -/
structure Outer (e : Env) (t : MachineState) (i : Nat) : Prop extends Regs e t where
  lt : i < e.bc.blocks.length
  x13 : t.getReg .x13 = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  ws : (t.getReg .x12).toNat = (e.st i).wordsStart
  ps : (t.getReg .x19).toNat = (e.st i).positionsStart
  bs : (t.getReg .x11).toNat = (e.st i).bytesStart
  total : (t.getReg .x5, t.getReg .x17, t.getReg .x16) = limbs (e.st i).total
  buckets : eListAt t e.bk 2048 = (e.st i).buckets

/-- Inside block `i`: its pointer, its `words_end` and the total so far saved in the frame. -/
structure Blk (e : Env) (t : MachineState) (i : Nat) : Prop extends Regs e t where
  lt : i < e.bc.blocks.length
  ptr : t.getMem (e.s.getReg .x2 - 1848) = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  we : t.getMem (e.s.getReg .x2 - 1888) = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8)
  total : (t.getMem (e.s.getReg .x2 - 1880), t.getMem (e.s.getReg .x2 - 1872),
    t.getMem (e.s.getReg .x2 - 1864)) = limbs (e.st i).total
  bs : (t.getReg .x11).toNat = (e.st i).bytesStart
  wsle : (e.st i).wordsStart ≤ (e.bc.blocks[i]'lt).wordsEnd
  wele : (e.bc.blocks[i]'lt).wordsEnd ≤ e.bc.words.length

/-- At word `j` of block `i` (`0x800110d0`). -/
structure WInv (e : Env) (t : MachineState) (i j : Nat) : Prop extends Blk e t i where
  jlo : (e.st i).wordsStart ≤ j
  jhi : j < (e.bc.blocks[i]'lt).wordsEnd
  x13 : t.getReg .x13 = e.wordsPtr + BitVec.ofNat 64 (16 * j)
  x12 : t.getReg .x12 = e.wordsPtr + BitVec.ofNat 64 (16 * (e.bc.blocks[i]'lt).wordsEnd)
  x6 : (t.getReg .x6).toNat = (e.wf i (j - (e.st i).wordsStart)).2
  buckets : eListAt t e.bk 2048 = (e.wf i (j - (e.st i).wordsStart)).1

/-- After block `i`'s words (`0x8001136c`). -/
structure Mid (e : Env) (t : MachineState) (i : Nat) : Prop extends Blk e t i where
  x19 : (t.getReg .x19).toNat =
    (e.wf i ((e.bc.blocks[i]'lt).wordsEnd - (e.st i).wordsStart)).2
  buckets : eListAt t e.bk 2048 =
    (e.wf i ((e.bc.blocks[i]'lt).wordsEnd - (e.st i).wordsStart)).1

end Rv64Verifier.Proofs.Bytecode.Eval
