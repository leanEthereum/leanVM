import Statement.Corollaries
import LeanVM.Protocol.LeanVMRpmAS
import LeanVM.Guest.ExperimentBridge
import LeanVM.Protocol.Keccak.RmfeDerive

/-!
# The end statements against their capped and literal forms

* **Query counts.** `KnowledgeSoundness` and `AggregateSound` hold for every `Q`, and
  `BatchingSound` for every `QA`; each is equivalent to its form capped at `2^128` queries, past
  which its bound exceeds `1` (`one_le_knowledgeSoundnessBound`, `one_le_batchingBound`).
* **The rate range.** `Completeness`, `GuestProverComplete`, the verifier's window and the honest
  prover all read `1..4` (`admissible_iff`, `queryTable_length`, `prove_eq_none_of_rate`).
* **The RMFE tables.** The statement's literals are the derivation's (`rmfe_eq_literal`).
* **LeanDA's shapes.** `logK`, `logM`, `cellSymbols`, `cellsPerRow` are reducible and unfold to
  their literals: the definitions they enter are their literal forms by `rfl`, and so are the end
  statements, which reach the shapes only through those definitions, `Fin (r * cellsPerRow)` and
  the adversaries' types (`leanDaPerfectlyComplete_iff_literal`, `leanDa_adversaries_eq_literal`).
  As `cellSymbols` and `cellsPerRow` are both `128`, no test by `rfl` tells the two apart.
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

/-! ## The rate range

`Completeness` and `GuestProverComplete` take `1 ≤ ρ ∧ ρ ≤ 4`, the range `MIN_LOG_INV_RATE ..
MAX_LOG_INV_RATE` of `whir.rs`, as the verifier's window and the honest prover's check do. -/

/-- The verifier's window, `Admissible`, is the stacking window and the rate range `1..4`. -/
theorem admissible_iff (μ ρ : ℕ) :
    Whir.Admissible μ ρ ↔ Whir.minLogStack ≤ μ ∧ μ ≤ Whir.maxLogStack ∧ 1 ≤ ρ ∧ ρ ≤ 4 :=
  Iff.rfl

/-- `queryTable` has one row per rate exponent of `1..4`. -/
theorem queryTable_length : Whir.queryTable.length = 4 :=
  rfl

/-- Outside `1..4` the honest prover makes no proof: a wider check in `LeanVM.Prover.prove` fails
here, a narrower one fails `Completeness`. -/
theorem prove_eq_none_of_rate {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) {ρ : ℕ} (fuel : ℕ)
    (h : ¬(1 ≤ ρ ∧ ρ ≤ 4)) : LeanVM.Prover.prove F prog input t ρ fuel = pure none := by
  unfold LeanVM.Prover.prove
  split
  · rfl
  · exact ite_eq_right h

/-! ## The RMFE tables

The statement's `rmfeEmbed` and `rmfeProject` are `RMFE_EMBED` and `RMFE_PROJECT` of
`crates/verifier/src/keccak.rs`, verbatim; `rmfe_eq` (`LeanVM/Protocol/Keccak/RmfeDerive.lean`)
proves them the tables the derivation computes. -/

theorem rmfe_eq_literal : rmfe = (rmfeEmbed, rmfeProject) := rmfe_eq

/-! ## LeanDA's shapes -/

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
    rowCell row j s = row ⟨128 * j + s, by show 128 * (j : ℕ) + s < 2 ^ 14; omega⟩ ∧
      cellsOfRows rows p s = (rows.getD (p / 128) []).getD (128 * (p % 128) + s) 0 :=
  ⟨rfl, rfl⟩

open LeanDa in
theorem leanDa_matrix_eq_literal {r : ℕ} (cells : Fin (r * 128) → Cell) (i : Fin r)
    (b : Fin (2 ^ 14)) (k j : ℕ) (message : Fin r → Payload) (p : Fin (r * 128)) :
    matrixRow cells i b =
        cells ⟨128 * i + b / 128, by have := i.isLt; have := b.isLt; omega⟩
          ⟨b % 128, Nat.mod_lt _ (by decide)⟩ ∧
      paddedCell cells k j =
        (if h : k < r ∧ j < 128 then cells ⟨128 * k + j, by omega⟩ else 0) ∧
      encodeMatrix message p =
        fun s : Fin 128 ↦ encodeRow (message ⟨p / 128, by have := p.isLt; omega⟩)
          ⟨128 * (p % 128) + s, by
            have := s.isLt; have := Nat.mod_lt p.val (show 0 < 128 by decide)
            show 128 * (p % 128 : ℕ) + s < 2 ^ 14; omega⟩ :=
  ⟨rfl, rfl, rfl⟩

open LeanDa in
theorem leanDa_membership_eq_literal (z : E) (b : Fin (2 ^ 14)) :
    dualCodewordAt z b = ∏ j : Fin 13,
      (1 + z ^ 2 ^ (j : ℕ) * ι ((AdditiveNTT.normalizedW (ZMod 2) basis
        (Fin.castLE (by omega) j)).eval (point b))) :=
  rfl

open LeanDa in
/-- `LeanDaPerfectlyComplete` with the shapes as literals. -/
def LeanDaPerfectlyCompleteLiteral : Prop :=
  ∀ (r : ℕ) (π : Equiv.Perm KeccakState) {Crs Proof : Type} (argument : LeanDaArgument r Crs Proof),
    r ≤ maxRows → argument.PerfectlyComplete (relationForPermutation r) →
      ∀ (message : Fin r → Fin (2 ^ 13) → E) (position : Fin (r * 128)),
        Pr{let b ← LeanDa.completenessExperiment r π argument message position}[b = true] = 1

theorem leanDaPerfectlyComplete_iff_literal :
    LeanDaPerfectlyCompleteLiteral ↔ LeanDa.LeanDaPerfectlyComplete :=
  Iff.rfl

open LeanDa in
/-- The binding adversaries' types with the shapes as literals: `LeanDaPositionBinding` and
`LeanDaCodeBinding` reach the shapes through them and through the games, whose positions and cells
are the definitions above. -/
theorem leanDa_adversaries_eq_literal (r : ℕ) (Crs Proof : Type) :
    PositionBindingAdversary r Crs Proof =
        (Unit × Crs → OracleComp Common.RandomPermutationOracles
          ((Common.DigestBytes × Proof) × Fin (r * 128) × (Fin 128 → E) × CellOpening ×
            (Fin 128 → E) × CellOpening)) ∧
      CodeBindingAdversary r Crs Proof =
        (Unit × Crs → OracleComp Common.RandomPermutationOracles
          ((Common.DigestBytes × Proof) × List (Fin (r * 128) × (Fin 128 → E) × CellOpening))) :=
  ⟨rfl, rfl⟩

end LeanVM.Statement.Windows
