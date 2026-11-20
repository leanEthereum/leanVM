/-
  Rv64mc.Spec.Walk.Repr

  How `walk`'s and `verify_execution`'s arguments and result sit in memory, as the Model holds them
  (`Model.BytecodeRust`, `Proof`), for objects in a caller's frame or the heap: the headers anywhere the caller
  owns (`Env.Owned`), everything they point to allocated before (`LiveVecAt`), so that every call keeps it.

  * `BytecodeAt env m a bc`: the `Bytecode` at `a` (`Layouts.Bytecode`): its length, its IV's 32 bytes, and its
    blocks, a `Vec<Vec<(K, Vec<u16>)>>` of each block's members (`Layouts.KVecU16`).
  * `ProofBodyAt env m q pf`: the `Proof` at `q`, its stream and openings as `Spec.Transcript.ProofAt` reads them,
    without `ProofAt.live`: `main` keeps its `Proof` in its frame, not in the heap.
  * `ResultOkAt m a`: the `Result<Summary, VerifierError>` at `a` is `Ok` (`Layouts.ResultSummary`, niche-encoded in
    the summary's first capacity: `Err` is the one tag `2^64 - 1`).
-/

import Rv64mc.Spec.Transcript.Repr
import Rv64mc.Model.Walk

namespace Rv64mc.Spec.Walk

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64mc.Spec.Transcript

/-- **The `u16`s `hs` from `a`**, half `k` at `a + 2k`, little-endian. -/
def HalvesAt (m : MachineState) (a : Word) (hs : List (BitVec 16)) : Prop :=
  a.toNat + 2 * hs.length < 2 ^ 64 ∧ ∀ k (h : k < hs.length),
    m.getByte (a + BitVec.ofNat 64 (2 * k + 1)) ++ m.getByte (a + BitVec.ofNat 64 (2 * k)) = hs[k]

/-- **A block's member `(word, positions)` at `a`**: the `K` and its `Vec<u16>` of positions. -/
def MemberAt (env : Env) (m : MachineState) (a : Word) (member : BitVec 64 × List (BitVec 16)) : Prop :=
  m.getMem (a + BitVec.ofNat 64 Layouts.KVecU16.f0) = member.1 ∧
    LiveVecAt env 2 HalvesAt m (a + BitVec.ofNat 64 Layouts.KVecU16.f1) member.2

/-- **A block at `a`**: a `Vec<(K, Vec<u16>)>` of its members. -/
def BlockAt (env : Env) (m : MachineState) (a : Word) (block : List (BitVec 64 × List (BitVec 16))) : Prop :=
  LiveVecAt env Layouts.KVecU16.byteSize (ArrayAt Layouts.KVecU16.byteSize (MemberAt env)) m a block

/-- **The `Bytecode` at `a` is `bc`.** A structure, so that `rv_auto` keeps it whole. -/
structure BytecodeAt (env : Env) (m : MachineState) (a : Word) (bc : Model.BytecodeRust) : Prop where
  len : m.getMem (a + BitVec.ofNat 64 Layouts.Bytecode.len) = BitVec.ofNat 64 bc.len
  iv : DigestAt m (a + BitVec.ofNat 64 Layouts.Bytecode.fiat_shamir_iv) bc.fiatShamirIv
  blocks : LiveVecAt env Layouts.Vec.byteSize (ArrayAt Layouts.Vec.byteSize (BlockAt env)) m
    (a + BitVec.ofNat 64 Layouts.Bytecode.blocks) bc.blocks

/-- **The `Proof` at `q` is `pf`**, wherever its header lies. -/
structure ProofBodyAt (env : Env) (m : MachineState) (q : Word) (pf : Proof) : Prop where
  stream : LiveVecAt env Layouts.E.byteSize EListAt m (q + BitVec.ofNat 64 Layouts.Proof.stream)
    (pf.stream.map Model.limbs)
  openings : LiveVecAt env Layouts.Vec.byteSize (ArrayAt Layouts.Vec.byteSize (PhaseAt env)) m
    (q + BitVec.ofNat 64 Layouts.Proof.merkle_openings) pf.openings

/-- **The `Result<Summary, VerifierError>` at `a` is `Ok`.** -/
def ResultOkAt (m : MachineState) (a : Word) : Prop :=
  m.getMem (a + BitVec.ofNat 64 Layouts.ResultSummary.tagOffset) ≠
    BitVec.ofNat 64 Layouts.ResultSummary.Err.tag

end Rv64mc.Spec.Walk
