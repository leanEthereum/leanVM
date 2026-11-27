/-
  LeanVM.Guest.WithHashBridge

  The guest's deployed definitions, over Keccak-f[1600] in the statement, are the proofs' forms with
  the deployed Keccak-256 and Keccak-f[1600] (`LeanVM.Guest.WithHash`).
-/

module

import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.WithHash
import LeanDa.WithHashBridge
import LeanDa.Commitment
public import Common.WithHash
public import LeanVM.Guest.AcceptableChild
public import LeanDa.WithHash

/-!
# The guest's deployed definitions are the forms with a hash

The statement's guest specification computes over Keccak-f[1600], Keccak-256 the sponge over it;
the proofs' forms take Keccak-256 as a function of its own. With Keccak-f[1600] in `Id` the sponge
is the deployed Keccak-256 (`keccak256With_keccakF1600`), so:

* the batching's run and the openings' climb (`runBatching_deployed`, `climbTo_eq_withHash`);
* LeanDA's commitment (`commitCells_keccakF1600`);
* the schemes' hash (`keccakHash_keccakF1600`): a digest read as the little-endian number of its 32
  bytes, the guest's reading.
-/

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- Keccak-256 over Keccak-f[1600], read as the schemes' hash output, is `keccakBits`. -/
theorem keccakHash_keccakF1600 :
    HashSig.OverPermutation.keccakHash (m := Id) keccakF1600 = Node.keccakBits := by
  funext input
  rw [HashSig.OverPermutation.keccakHash, keccak256With_keccakF1600]
  rfl

namespace Da

/-- LeanDA's hash over Keccak-f[1600] is Keccak-256 as LeanDA's hash. -/
theorem hashOver_keccakF1600 : LeanDa.hashOver keccakF1600 = keccak256Bytes := rfl

/-- The statement's commitment to the matrix of codewords `rows` is the crate's, computed level by
level (`LeanDa.commitCodewords_eq_commitCells`). -/
theorem commitCells_keccakF1600 (rows : List (List E))
    (hrows : ∀ row ∈ rows, row.length = 2 ^ LeanDa.logM) (hle : rows.length ≤ LeanDa.maxRows) :
    LeanDa.commitCells keccakF1600 (LeanDa.cellsOfRows rows) =
      LeanDa.commitCodewordsWithHash keccak256Bytes rows := by
  rw [LeanDa.commitCells_eq_withHash, hashOver_keccakF1600,
    LeanDa.commitCodewords_eq_commitCells _ rows hrows hle]

end Da

namespace Guest

theorem Batch.runBatching_deployed (prog : VerifierProgram Bool) (proof : Proof) :
    Batch.runBatching (m := Id) keccakF1600 prog proof =
      Batch.runBatchingWithHash (m := Id) keccak256 keccakF1600 prog proof := by
  simp only [Batch.runBatching, Batch.runBatchingWithHash, runProof_eq_withHash,
    keccak256With_keccakF1600]

theorem Limits.climbTo_eq_withHash (node : Digest) (q : ℕ) (path : List Digest) :
    Limits.climbTo node q path = Id.run (climbWithHash (m := Id) keccak256 node q path) := by
  rw [Limits.climbTo, climb_eq_withHash, keccak256With_keccakF1600]

end Guest

end LeanVM

end
