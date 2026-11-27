import Statement.Corollaries
import LeanVM.Protocol.LeanVMRpmAS

/-!
# The end statements against their capped forms

* **Query counts.** `KnowledgeSoundness` and `AggregateSound` hold for every `Q`; each is
  equivalent to its form capped at `2^128` queries, past which its bound exceeds `1`
  (`one_le_knowledgeSoundnessBound`).
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

end LeanVM.Statement.Windows
