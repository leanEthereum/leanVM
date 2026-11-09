module

public import Statement.Theorems

/-!
# Corollaries

End statements that follow from `Statement.Theorems`, stated in their composed form: what an
accepted proof of the leanISA guest program establishes (`AggregateSound`). `lean_vm` proves
`LeanVM.corollaries_of_theorems`, that `Statement.Theorems` implies `Statement.Corollaries` for the
same extractor and decoder programs, from the fields of `Theorems` alone, and
`LeanVM.corollaries_hold`. A reviewer who trusts `Theorems` need not read this file.
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- **The decoding `decoding` explains the statement `statement`**: it is the deployed seed,
`statement` and a witness holding `statement`; or the decoded seed and statement, with the deployed
seed and `statement`, give a Keccak-256 collision among the candidates. -/
def ExplainsStatement (guest : LeanIsaProgram) (statement : NodeStatement)
    (decoding : SeedStatementAndWitness) : Prop :=
  (decoding.seed = deployedSeed guest ∧ decoding.statement = statement ∧
      NodeRelation (bytecodeWords guest) (deployedSeed guest) statement decoding.witness) ∨
    HasCollision
      (collisionCandidates decoding.seed decoding.statement (deployedSeed guest) statement)

open OracleComp OracleSpec in
/-- **The outer verifier's acceptance, explained.** In the random-permutation experiment of
`LeanVm.lean`, the adversary, querying `π` and `π⁻¹`, outputs a proof. The event: the verifier
accepts it as a proof of `guest` on the digest, under the deployed seed, of a statement `statement`
whose deferred claim holds of the guest program's bytecode (`DeferredClaim.HoldsWithShape`, as the
deployed outer verifier checks by recomputing it), and yet the execution the knowledge extractor
`extractor` reads off the adversary's transcript and the proof does not explain `statement`: no
execution is extracted, or the decoder program `guestWitnessDecoder`, run on it within its budget
(`LeanVmGuest.lean`), outputs the encoding of no decoding that explains `statement`
(`ExplainsStatement`). It composes `KnowledgeSoundness`, `GuestKnowledgeSoundness` and
`StatementDigestBinds`; its probability is at most the bound of `KnowledgeSoundness`,
`(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256`, for `Q ≤ 2^128` queries to `π`, `π⁻¹`.

Keccak-256 and Keccak-f[1600] outside the executed program are built from `π`, so the verifier
seeds its transcript with the IV over `π`; the statement's digest, its seed (`deployedSeed`, the IV
over the deployed Keccak-f[1600]) and the collisions are of the deployed Keccak-256, which the guest
program computes. A child's claims carry knowledge only through its fresh claim, which this
statement does not make true: the root's deferred claim holds, but the batching that ties it to the
children's fresh claims is sound only outside the circuit (`LeanVmGuest.lean`). -/
def AggregateSound (guest : LeanIsaProgram) (guestWitnessDecoder : LeanVM.Cost.MachineProgram)
    (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperiment adversary}[∃ statement : NodeStatement,
      outcome.accepted ∧ outcome.program = guest ∧
      publicInputDigest outcome.input = statementDigest (deployedSeed guest) statement ∧
      statement.deferredClaim.HoldsWithShape (bytecodeWords guest) ∧
      ¬ ∃ execution, ∃ decoding : SeedStatementAndWitness,
        extractor outcome.program outcome.input outcome.transcript outcome.proof = some execution ∧
        Cost.outputWithin guestWitnessDecoder guestWitnessDecoderSizeBound
          (guestWitnessDecoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput outcome.program execution) =
            some (Cost.encodeValue decoding) ∧
        ExplainsStatement guest statement decoding] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM.Node

namespace Statement

/-- **The corollaries**, each following from `Theorems`, for the same extractor and decoder
programs (two parameters of the same type: every use names them). -/
structure Corollaries
    (leanVmKnowledgeExtractor guestWitnessDecoder : LeanVM.Cost.MachineProgram) : Prop where
  /-- An accepted proof of the leanISA guest program on the digest of `s` under the deployed seed,
  `s`'s deferred claim holding, is explained by the execution the extractor program extracts (the
  decoder program outputs, on it, the encoding of that seed, `s` and a witness holding `s`) or by a
  Keccak-256 collision, except with the bound of `leanVmKnowledgeSoundness`: from
  `leanVmKnowledgeSoundness`, `guestKnowledgeSoundness` and `statementDigestBinds`. Claims held
  through children carry no knowledge of their own (`AggregateSound`). -/
  aggregateSound : LeanVM.Node.AggregateSound LeanVM.Guest.guestProgram guestWitnessDecoder
    (LeanVM.extractorComputedBy leanVmKnowledgeExtractor)

end Statement

end
