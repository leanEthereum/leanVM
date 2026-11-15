/-
  LeanVM.Guest.WithHashBridge

  The guest's deployed definitions, over Keccak-f[1600] in the statement, are the proofs' forms with
  the deployed Keccak-256 and Keccak-f[1600] (`LeanVM.Guest.WithHash`).
-/

module

public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.WithHash
public import LeanDa.WithHashBridge
public import LeanDa.Commitment
public import Common.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The guest's deployed definitions are the forms with a hash

The statement's guest specification computes over Keccak-f[1600], Keccak-256 the sponge over it;
the proofs' forms take Keccak-256 as a function of its own. With Keccak-f[1600] in `Id` the sponge
is the deployed Keccak-256 (`keccak256With_keccakF1600`), so:

* the batching's run, the verifier refusing a zero challenge, the deferring verifier refusing a zero
  challenge, the openings' climb (`runBatching_deployed`, …);
* LeanDA's commitment (`commitCells_keccakF1600`);
* leanXMSS's verification (`xmssVerify_eq_withHash`): the scheme reads a digest as the
  little-endian number of its 32 bytes, the guest's reading (`keccakHash_keccakF1600`); the
  statement's leanSPHINCS is written over the permutation alone.
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

/-- The statement's leanXMSS verification over `π` is the hash-query one with the hash Keccak-256
over `π`. -/
theorem xmss_verify_eq_verifyWithHash {m : Type → Type} [Monad m]
    (π : KeccakState → m KeccakState) (pk : HashSig.PublicKey) (message : HashSig.Message)
    (σ : LeanXmss.Signature) :
    LeanXmss.Verification.verify π pk message σ =
      @LeanXmss.Verification.verifyWithHash m _ ⟨HashSig.OverPermutation.keccakHash π⟩ pk message
          σ := rfl

namespace Node

/-- leanXMSS verification over Keccak-f[1600] is the hash-query verification with `keccakBits`. -/
theorem xmssVerify_eq_withHash (pk : HashSig.PublicKey) (message : HashSig.Message)
    (σ : LeanXmss.Signature) :
    LeanXmss.verifyWithKeccak pk message σ =
      Id.run (@LeanXmss.Verification.verifyWithHash Id _ ⟨keccakBits⟩ pk message σ) := by
  rw [LeanXmss.verifyWithKeccak, xmss_verify_eq_verifyWithHash, keccakHash_keccakF1600]

end Node

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

theorem Budget.verifierRefusingZero_deployed (prog : LeanIsaProgram) (input : PublicInput)
    (proof : Proof) :
    Completeness.verifierRefusingZero (m := Id) keccakF1600 prog input proof =
      Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 prog input proof := by
  simp only [Completeness.verifierRefusingZero, Budget.verifierRefusingZeroWithHash, seedWith_eq_withHash,
    runProof_eq_withHash, keccak256With_keccakF1600]

theorem Limits.verifyDeferredRefusingZero_eq_withHash (bytecode : List K) (iv publicInput : Digest)
    (c : BytecodeClaim) (π : Proof) :
    Limits.verifyDeferredRefusingZero bytecode iv publicInput c π =
      Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
        (deferringVerifierProgram c bytecode publicInput).refusingZeroChallenge
        (keccakF1600 (seedInput iv publicInput)) π) := by
  rw [Limits.verifyDeferredRefusingZero, runProof_eq_withHash, keccak256With_keccakF1600]

theorem Limits.climbTo_eq_withHash (node : Digest) (q : ℕ) (path : List Digest) :
    Limits.climbTo node q path = Id.run (climbWithHash (m := Id) keccak256 node q path) := by
  rw [Limits.climbTo, climb_eq_withHash, keccak256With_keccakF1600]

end Guest

end LeanVM

end
