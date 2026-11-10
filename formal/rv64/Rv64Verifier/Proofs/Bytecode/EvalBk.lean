import Rv64Verifier.Proofs.Bytecode.EvalCreditObl
import Rv64Verifier.Proofs.Bytecode.EvalZero

/-!
# `Bytecode::evaluate`: a block's buckets into its bit sums

`0x80011394` reads `block.bytes_end`, trapping unless `bytes_start <= bytes_end`, `0x8001139c`
unless `bytes_end <= bytes.len()`; `0x800113a4` saves it and skips the buckets if there are none;
`0x800113ac` sets up the walk (`BkInv`). Per bucket (`bk_body`): `lhu` loads it (`0x800113c8`),
trapping unless `< 2048`; `0x800113d0` takes the bucket's sum and zeroes it; `0x80011408` credits
the sum to the bit sums (`credit`); `0x80011608` restores registers and loops. At the end,
`BkDone`, the hypothesis of `EvalTail.lean`'s `Tail`.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

namespace Env

/-- Block `i`. -/
def blk (e : Env) (i : Nat) : BlockRust := e.bc.blocks.getD i ⟨0, 0, 0⟩

/-- Where block `i`'s positions end. -/
def pe (e : Env) (i : Nat) : Nat := (e.wf i ((e.blk i).wordsEnd - (e.st i).wordsStart)).2

/-- Block `i`'s buckets, folded from its start, after `k` of them. -/
def bf (e : Env) (i k : Nat) : List E × List E :=
  ((e.bc.bytes.drop (e.st i).bytesStart).take k).foldl bucketStepRust
    ((e.wf i ((e.blk i).wordsEnd - (e.st i).wordsStart)).1, List.replicate 64 0)

end Env

theorem blk_eq (e : Env) {i : Nat} (hi : i < e.bc.blocks.length) : e.blk i = e.bc.blocks[i] :=
  List.getD_eq_getElem _ _ hi

/-- At bucket `b` of block `i` (`0x800113c8`). -/
structure BkInv (e : Env) (t : MachineState) (i b : Nat) : Prop extends Regs e t where
  lt : i < e.bc.blocks.length
  ptr : t.getMem (e.s.getReg .x2 - 1848) = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  next : t.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1))
  we : t.getMem (e.s.getReg .x2 - 1888) =
    e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8)
  be : t.getMem (e.s.getReg .x2 - 1856) =
    e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16)
  total : (t.getMem (e.s.getReg .x2 - 1880), t.getMem (e.s.getReg .x2 - 1872),
    t.getMem (e.s.getReg .x2 - 1864)) = limbs (e.st i).total
  s3 : (t.getMem (e.s.getReg .x2 - 1792)).toNat = e.pe i
  x19 : (t.getReg .x19).toNat = e.pe i
  blo : (e.st i).bytesStart ≤ b
  bhi : b < (e.blk i).bytesEnd
  bend : (e.blk i).bytesEnd ≤ e.bc.bytes.length
  x10 : t.getReg .x10 = e.bytesPtr + BitVec.ofNat 64 (2 * b)
  x11 : (t.getReg .x11).toNat = 2 * ((e.blk i).bytesEnd - b)
  buckets : eListAt t e.bk 2048 = (e.bf i (b - (e.st i).bytesStart)).1
  sums : eListAt t (e.s.getReg .x2 - 1688) 64 = (e.bf i (b - (e.st i).bytesStart)).2

/-- After block `i`'s buckets (`0x80011618`). -/
structure BkDone (e : Env) (t : MachineState) (i : Nat) : Prop extends Regs e t where
  lt : i < e.bc.blocks.length
  ptr : t.getMem (e.s.getReg .x2 - 1848) = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  next : t.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1))
  we : t.getMem (e.s.getReg .x2 - 1888) =
    e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8)
  be : t.getMem (e.s.getReg .x2 - 1856) =
    e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16)
  total : (t.getMem (e.s.getReg .x2 - 1880), t.getMem (e.s.getReg .x2 - 1872),
    t.getMem (e.s.getReg .x2 - 1864)) = limbs (e.st i).total
  x19 : (t.getReg .x19).toNat = e.pe i
  blo : (e.st i).bytesStart ≤ (e.blk i).bytesEnd
  bend : (e.blk i).bytesEnd ≤ e.bc.bytes.length
  buckets : eListAt t e.bk 2048 =
    (e.bf i ((e.blk i).bytesEnd - (e.st i).bytesStart)).1
  sums : eListAt t (e.s.getReg .x2 - 1688) 64 =
    (e.bf i ((e.blk i).bytesEnd - (e.st i).bytesStart)).2

/-- Writing element `idx` of a list of `E`s, its other elements kept. -/
theorem eListAt_set' {s t : MachineState} {p : Word} {n idx : Nat} (hidx : idx < n)
    (hw : p.toNat + 24 * n ≤ 2 ^ 64) {v : E}
    (hv : eAt t (p + BitVec.ofNat 64 (24 * idx)) = v)
    (hother : ∀ a, Within a p (24 * n) → ¬ Within a (p + BitVec.ofNat 64 (24 * idx)) 24 →
      t.getMem a = s.getMem a) :
    eListAt t p n = (eListAt s p n).set idx v := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  rw [List.getElem_set]
  split
  · rename_i h; subst h; rw [eListAt_getElem, hv]
  · rename_i h
    rw [eListAt_getElem, eListAt_getElem]
    simp only [eListAt_length] at h1
    unfold eAt
    rw [hother _ (by addr_omega [hidx, h1, hw]) (by addr_omega [hidx, h1, hw, h]),
      hother _ (by addr_omega [hidx, h1, hw]) (by addr_omega [hidx, h1, hw, h]),
      hother _ (by addr_omega [hidx, h1, hw]) (by addr_omega [hidx, h1, hw, h])]

theorem bf_zero (e : Env) (i : Nat) :
    e.bf i 0 = ((e.wf i ((e.blk i).wordsEnd - (e.st i).wordsStart)).1, List.replicate 64 0) := by
  simp [Env.bf]

theorem bf_succ (e : Env) {i b : Nat} (h1 : (e.st i).bytesStart ≤ b) (h2 : b < e.bc.bytes.length) :
    e.bf i (b + 1 - (e.st i).bytesStart) =
      bucketStepRust (e.bf i (b - (e.st i).bytesStart)) e.bc.bytes[b] := by
  rw [Env.bf, take_drop_succ _ h1 h2, List.foldl_append]
  rfl

end Rv64Verifier.Proofs.Bytecode.Eval
