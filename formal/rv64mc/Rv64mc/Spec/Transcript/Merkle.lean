/-
  Rv64mc.Spec.Transcript.Merkle

  The contract of `Transcript::merkle(&mut self, root: Digest, block_length: u64, queries: &[u64],
  leaf_words: usize) -> Result<Vec<&[K]>, VerifierError>`: the result's slot (`sret`) in `a0`, the transcript in `a1`
  (as `next_scalar`'s), the root by reference in `a2`, the block length in `a3`, the queries as a pointer and a length
  in `a4`, `a5`, the leaf's words in `a6`. It is the mirror's `Model.TM.merkle`: where the mirror returns the leaves
  and `t'`, the slot holds `Ok` of a fresh `Vec` of slices, slice `k` the words of leaf `k` (in the proof's memory),
  and the transcript is `t'`; where it fails, the slot holds `Err` (the vector's niche, `Layouts.ResultVecE`'s). It
  writes the slot and the opening offset (`Out`).
-/

import Rv64mc.Spec.Transcript.NextScalar

namespace Rv64mc.Spec.Transcript.Merkle

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The slice `&[u64]` at `a` holds `ws`**: its pointer's words, its length. -/
def SliceWordsAt (m : MachineState) (a : Word) (ws : List Word) : Prop :=
  WordsAt m (m.getMem (a + BitVec.ofNat 64 Layouts.SliceE.ptr)) ws ∧
    m.getMem (a + BitVec.ofNat 64 Layouts.SliceE.len) = BitVec.ofNat 64 ws.length

def Pre (env : Env) (t : Model.TState) (root : List (BitVec 8)) (qs : List Word) (regs : Reg → Word)
    (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ NextScalar.SlotArgs env Layouts.ResultVecE.byteSize regs m ∧
    DigestAt m (regs .x12) root ∧ Safe env m (regs .x2) (regs .x12) Layouts.Digest.byteSize ∧
    SliceArgs WordsAt m (regs .x14) (regs .x15) qs ∧ env.Live m (regs .x14) (8 * qs.length)

def Post (env : Env) (t : Model.TState) (root : List (BitVec 8)) (qs : List Word) (regs : Reg → Word)
    (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  match (Model.TM.merkle root (regs .x13) qs (regs .x16).toNat).run t with
  | some (rows, t') =>
    (∃ ptr cap, VecAt (ArrayAt Layouts.SliceE.byteSize SliceWordsAt) m' (regs .x10) ptr cap rows ∧
      (cap = 0 ∨ env.Fresh m m' ptr (Layouts.SliceE.byteSize * cap))) ∧ TranscriptAt env m' (regs .x11) t'
  | none => m'.getMem (regs .x10 + BitVec.ofNat 64 Layouts.ResultVecE.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultVecE.Err.tag

/-- What it writes besides its stack and its allocations: the slot and the opening offset. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.ResultVecE.byteSize b ∨
    b = regs .x11 + BitVec.ofNat 64 Layouts.Transcript.opening_offset

/-- **The contract of `Transcript::merkle`**, function `i` of `p` with `need` bytes of stack (its frame is 80 bytes;
    it calls `MerklePath::root`, `memcmp`, `try_allocate_in` and `handle_error`), for every transcript state, root
    and queries. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t root qs, Holds env p i need (Pre env t root qs) (Post env t root qs) Out

end Rv64mc.Spec.Transcript.Merkle
