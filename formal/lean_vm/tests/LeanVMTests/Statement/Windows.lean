import Statement.Corollaries
import LeanVM.Protocol.LeanVMRpmAS
import LeanVM.Guest.ExperimentBridge

/-!
# The statement's changes, old against new

Each change to an end statement of `Statement/` is checked here: the old definition, restated, is
equivalent to the new one (a strengthening proved by the proofs' lemmas), or implied by it.

* **Query caps.** `KnowledgeSoundness` and `AggregateSound` held for `Q ≤ 2^128` queries and
  `BatchingSound` for `QA ≤ 2^128`; past those counts their bounds exceed `1`
  (`one_le_knowledgeSoundnessBound`, `one_le_batchingBound`), so dropping the caps changes nothing.
* **Named constants.** The rate range `1..4` is `Whir.minLogInvRate .. Whir.maxLogInvRate`, and
  LeanDA's shapes are `logK`, `logM`, `cellSymbols` and `cellsPerRow`: each old form is the new
  one by `rfl`.
-/

open scoped ENNReal
open OracleComp OracleSpec

namespace LeanVM.Statement.Windows

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch

/-! ## Query caps -/

/-- `KnowledgeSoundness` with its former cap `Q ≤ 2^128`. -/
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
      prEvent_le_of_one_le _ (one_le_knowledgeSoundnessBound hQ),
    fun h A Q hA _ ↦ h A Q hA⟩

/-- `AggregateSound` with its former cap `Q ≤ 2^128`. -/
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
      prEvent_le_of_one_le _ (one_le_knowledgeSoundnessBound hQ),
    fun h A Q hA _ ↦ h A Q hA⟩

/-- `BatchingSound` with its former cap `QA ≤ 2^128`. -/
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
  ⟨fun h M b hb hM A QA hA hQV ↦ (le_or_gt QA (2 ^ 128)).elim (fun hQA ↦ h M b hb hM A QA hA hQA hQV)
      fun hQA ↦ prEvent_le_of_one_le _ (one_le_batchingBound hQA),
    fun h M b hb hM A QA hA _ hQV ↦ h M b hb hM A QA hA hQV⟩

/-! ## Named constants -/

theorem admissible_iff_literal (μ ρ : ℕ) :
    Whir.Admissible μ ρ ↔
      Whir.minLogStack ≤ μ ∧ μ ≤ Whir.maxLogStack ∧ 1 ≤ ρ ∧ ρ ≤ 4 :=
  Iff.rfl

theorem ladder_eq_literal (μ ρ : ℕ) :
    Whir.ladder μ ρ =
      if Whir.Admissible μ ρ then
        let geometry := Whir.ladderShape μ ρ
        let queries := (Whir.queryTable.getD (ρ - 1) []).getD (μ - Whir.minLogStack) []
        if geometry.length = queries.length then
          some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
        else none
      else none :=
  rfl

/-- `Completeness` with the rate range as literals. -/
def CompletenessLiteral : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 30 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperiment leanVmHonestProver program input execution ρ (2 ^ 35)}[
        v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

theorem completeness_iff_literal : CompletenessLiteral ↔ Completeness := Iff.rfl

/-- The rate hypothesis of `Completeness` and `GuestProverComplete` is satisfiable. -/
theorem rate_range_nonempty : ∃ ρ, Whir.minLogInvRate ≤ ρ ∧ ρ ≤ Whir.maxLogInvRate :=
  ⟨1, by decide⟩

theorem guestProverComplete_rate_eq :
    (∀ ρ : ℕ, Whir.minLogInvRate ≤ ρ ∧ ρ ≤ Whir.maxLogInvRate ↔ 1 ≤ ρ ∧ ρ ≤ 4) :=
  fun _ ↦ Iff.rfl

open LeanDa in
theorem leanDa_shapes_eq_literal :
    Payload = (Fin (2 ^ 13) → E) ∧ Row = (Fin (2 ^ 14) → E) ∧ Cell = (Fin 128 → E) :=
  ⟨rfl, rfl, rfl⟩

open LeanDa in
theorem leanDa_positions_eq_literal {r : ℕ} (i : Fin r) (j : Fin 128) (p : Fin (r * 128)) :
    (cellPosition i j).val = 128 * i + j ∧ (positionRow p).val = p / 128 ∧
      (positionCell p).val = p % 128 :=
  ⟨rfl, rfl, rfl⟩

open LeanDa in
theorem leanDa_rows_eq_literal (row : Row) (j : Fin 128) (s : Fin 128) (rows : List (List E))
    (p : Fin (rows.length * 128)) :
    rowCell row j s = row ⟨128 * j + s, by omega⟩ ∧
      cellsOfRows rows p s = (rows.getD (p / 128) []).getD (128 * (p % 128) + s) 0 :=
  ⟨rfl, rfl⟩

end LeanVM.Statement.Windows
