import Statement.Corollaries
import LeanVM.Protocol.LeanVMRpmAS
import LeanVM.Guest.Batch.Rpm

/-!
# The end statements against their capped forms

* **Query counts.** `KnowledgeSoundness` and `AggregateSound` hold for every `Q`, and
  `BatchingSound` for every `QA`; each is equivalent to its form capped at `2^128` queries, past
  which its bound exceeds `1` (`one_le_knowledgeSoundnessBound`, `one_le_batchingBound`).
-/

open scoped ENNReal
open OracleComp OracleSpec

namespace LeanVM.Statement.Windows

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch

/-! ## Query counts -/

/-- `KnowledgeSoundness` capped at `Q ≤ 2^128`. -/
def KnowledgeSoundnessCapped (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperiment adversary}[
        BreaksKnowledgeSoundness extractor outcome] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

theorem knowledgeSoundness_iff_capped (extractor : StraightLineExtractor) :
    KnowledgeSoundnessCapped extractor ↔ KnowledgeSoundness extractor :=
  ⟨fun h A Q hA ↦ (le_or_gt Q (2 ^ 128)).elim (h A Q hA) fun hQ ↦
      (prEvent_le_one _).trans (one_le_knowledgeSoundnessBound hQ),
    fun h A Q hA _ ↦ h A Q hA⟩

/-- `AggregateSound` capped at `Q ≤ 2^128`. -/
def AggregateSoundCapped (guest : LeanIsaProgram) (guestWitnessDecoder : LeanVM.Cost.MachineProgram)
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
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

theorem aggregateSound_iff_capped (guest : LeanIsaProgram) (decoder : LeanVM.Cost.MachineProgram)
    (extractor : StraightLineExtractor) :
    AggregateSoundCapped guest decoder extractor ↔ AggregateSound guest decoder extractor :=
  ⟨fun h A Q hA ↦ (le_or_gt Q (2 ^ 128)).elim (h A Q hA) fun hQ ↦
      (prEvent_le_one _).trans (one_le_knowledgeSoundnessBound hQ),
    fun h A Q hA _ ↦ h A Q hA⟩

/-- `BatchingSound` capped at `QA ≤ 2^128`. -/
def BatchingSoundCapped : Prop :=
  ∀ (M : ℕ) (bytecode : List K), bytecode.length = 2 ^ Nat.log2 bytecode.length →
    M ≤ 2 ^ 64 - 1 →
    ∀ (adversary : OracleComp Common.RandomPermutationOracles (Unit × Proof)) (QA : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost QA → QA ≤ 2 ^ 128 →
    batchingQueryBound bytecode M ≤ 2 ^ 96 →
    Pr{let outcome ← Common.runWithRandomPermutation (do
         let output ← adversary
         let accepted ←
           runBatching Common.queryPermutation (boundedBatchingProgram M bytecode) output.2
         return (output, accepted))}[
      outcome.2 = true ∧ SomeChildClaimFalse bytecode M outcome.1.2] ≤
      (((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) *
          (2 : ℝ≥0∞)⁻¹ ^ 130 +
        5 * ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

theorem batchingSound_iff_capped : BatchingSoundCapped ↔ BatchingSound :=
  ⟨fun h M b hb hM A QA hA hQV ↦ (le_or_gt QA (2 ^ 128)).elim
      (fun hQA ↦ h M b hb hM A QA hA hQA hQV)
      fun hQA ↦ (prEvent_le_one _).trans (one_le_batchingBound hQA),
    fun h M b hb hM A QA hA _ hQV ↦ h M b hb hM A QA hA hQV⟩

end LeanVM.Statement.Windows
