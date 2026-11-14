/-
  LeanVM.Guest.WithHash

  The guest's definitions with Keccak-256 a call or a function of its own, beside the permutation:
  the batching's run and the verifier refusing a zero challenge with a hash `H`, the deployed
  hashes as LeanDA's bytes and the schemes' bits, and the guest's statements in the experiments
  with the two calls (`LeanVM.Protocol.WithHash`). The statement's are over the permutation alone
  (`Statement/LeanVmGuest.lean`); `LeanVM.Guest.WithHashBridge` proves them these.
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

@[expose] public section

open scoped ENNReal

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- Keccak-256 as LeanDA's hash: the digest's 32 bytes (`Digest.toBytes`). -/
def keccak256Bytes (input : List UInt8) : Common.DigestBytes := (keccak256 input).toBytes

end LeanVM.Da

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A digest as the schemes' 256-bit hash output: its 32 bytes as a little-endian number. -/
def digestBits (d : Digest) : BitVec 256 :=
  BitVec.ofNat 256 ((digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- Keccak-256 as the schemes' hash. -/
def keccakBits (input : List UInt8) : BitVec 256 := digestBits (keccak256 input)

end LeanVM.Node

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-- **The batching transcript run**, for a hash function `H` and a permutation `F` in any monad:
from the seed `F(H(label) ‖ 0)` (`FiatShamirState::from_label`; the guest program bakes its
capacity, `AGG_SEED_*`, `aggregation.rs`), the program on the proof. -/
noncomputable def runBatchingWithHash {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) (prog : VerifierProgram Bool) (proof : Proof) : m Bool := do
  let seed ← F (seedInput (← H batchingLabel) (Vector.replicate 4 0))
  runProofWithHash H F prog seed proof

end LeanVM.Guest.Batch

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

namespace Budget

open LeanVM.Guest.Completeness

open Coverage

/-- **The leanVM verifier refusing a zero challenge** (`VerifierProgram.refusingZeroChallenge`):
`verifier H F` with every sampled challenge `0` a failure. -/
def verifierRefusingZeroWithHash {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool := do
  let seed ← seedWithHash H F (bytecodeWords prog) (publicInputDigest input)
  runProofWithHash H F
    (do
      verifyExecution computedBytecodeValue (bytecodeWords prog) (publicInputDigest input)
      return true : VerifierProgram Bool).refusingZeroChallenge
        seed proof

/-- Keccak-256 and Keccak-f[1600] answering the calls `KeccakCalls`. -/
def deployedKeccakCalls : QueryImpl KeccakCalls Id
  | .inl x => keccak256 x
  | .inr s => keccakF1600 s

open OracleComp in
/-- **An honest prover's proof with the deployed Keccak-256 and Keccak-f[1600].** -/
def honestProofWithDeployedKeccakWithHash (proverWithHash : HonestProverWithHash) (prog :
    LeanIsaProgram)
    (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) : Option Proof :=
  Id.run (simulateQ deployedKeccakCalls (proverWithHash prog input t ρ fuel))

open OracleComp OracleSpec in
/-- **The honest proof of an execution of the guest program is a child the guest program accepts**:
for the honest prover `LeanVM.leanVmHonestProver` (`LeanVm.lean`, `LeanVM.Prover.prove` with the
oracle calls),
1. in the random-permutation model, at `2^35` nonces per proof of work, it makes no proof, or
   `verifierRefusingZero` rejects its proof, of a valid execution of committed size at most
   `2^30`, at an inverse rate `2^ρ`, `1 ≤ ρ ≤ 4`, with probability at most `2^-100`;
2. its proof with the deployed Keccak (`honestProofWithDeployedKeccak`), if it makes one, of an
   execution of the leanISA guest program on a statement's digest under the deployed seed, wherever `verifierRefusingZero` with the deployed Keccak accepts it,
   forms with the statement (its deferred claim shaped) and some true claim `freshClaim` on the
   bytecode (`fresh.Holds`) a child the guest program accepts (`AcceptableChild`).
Reading part 1 for the deployed Keccak, so that part 2 applies to the honest proof, is the heuristic
that the deployed Keccak-f[1600] behaves as a random permutation, applied to this prover.
Proved by `LeanVM.Guest.Budget.guest_child_complete`. -/
def GuestChildCompleteWithHash : Prop :=
  (∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 30 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← (simulateQ LeanVM.keccakCallsOverRandomPermutation (do
        match ← LeanVM.proverWithHash prog input t ρ (2 ^ 35) with
        | none => pure false
        | some proof =>
          verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)).run' []}[v =
          false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 100) ∧
  ∀ (s : NodeStatement) (t : Execution guestProgram) (ρ : ℕ),
    s.deferredClaim.HasBytecodeShape (bytecodeWords guestProgram) →
    let input := PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) s)
    ∀ proof,
      honestProofWithDeployedKeccakWithHash LeanVM.proverWithHash guestProgram input t ρ (2 ^ 35) =
        some proof →
    verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 guestProgram input proof = true →
    ∃ fresh, fresh.Holds (bytecodeWords guestProgram) ∧
      AcceptableChild (bytecodeWords guestProgram) (deployedSeed guestProgram) ⟨s, fresh, proof⟩

end Budget

namespace Batch

open LeanVM.Rpm OracleComp OracleSpec in
/-- **The batching in the random-permutation model.** For a bytecode of power-of-two length and
a bound `M ≤ 2^64 - 1` on the children's count: an adversary of `QA` queries to `π` and `π⁻¹`
outputs a proof; the probability that the batching's verifier, Keccak-256 the sponge over `π` and
Keccak-f[1600] `π`, accepts it while its stream begins with fewer than `M` children of the
bytecode's shapes one of whose claims is false is at most
`(QA + QV + 1) · max(2M - 3, 8) · 2^-130 + 5 (QA + QV)² · 2^-256`, for `QA ≤ 2^128` and the
program's query bound `QV = batchingQueryBound bytecode M ≤ 2^96`; the adversary's private coins
are free (`BatchingSound`'s bound, which says where the factor comes from).

This is the batching run outside the circuit, with Keccak-f[1600] = `π`; it does not compose with
the guest program's in-circuit statements, whose `KECCAK` instruction computes the deployed
Keccak-f[1600], so soundness across recursion levels does not follow from it. -/
def BatchingSoundWithHash : Prop :=
  ∀ (M : ℕ) (bytecode : List K), bytecode.length = 2 ^ Nat.log2 bytecode.length →
    M ≤ 2 ^ 64 - 1 → ∀ (A : OracleComp Common.RandomPermutationOracles (Unit × Proof)) (QA : ℕ),
    Common.QueryCostAtMost A Common.permutationCallCost QA → QA ≤ 2 ^ 128 →
    batchingQueryBound bytecode M ≤ 2 ^ 96 →
    Pr{let z ← runAdversaryThen A fun z ↦
         runBatchingWithHash callKeccak256 callKeccakF1600 (boundedBatchingProgram M bytecode) z.2}[
      z.1.2 = true ∧ SomeChildClaimFalse bytecode M z.1.1.2] ≤
      (((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) *
          (2 : ℝ≥0∞)⁻¹ ^ 130 +
        5 * ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end Batch

end LeanVM.Guest

end
