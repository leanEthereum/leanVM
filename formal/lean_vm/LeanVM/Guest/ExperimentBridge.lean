module

public import LeanVM.Protocol.ExperimentBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Protocol.ToVCVio.PrEvent
import LeanVM.Prover.Refine

@[expose] public section

/-!
# The guest's statements over `π` are the statements with the two calls

The statement's batching run is over a permutation alone; with the hash Keccak-256 over it it is
the form with a hash (`runBatching_eq_withHash`). The statement's experiments are games in the
model's oracles; the proofs' run the two calls against the model
(`LeanVM.Protocol.ExperimentBridge`):

* `honestProofWithDeployedKeccak_eq_withHash`: the honest prover's proof with the deployed
  Keccak-f[1600] is the two-call prover's with the deployed Keccak;
* `batchingSound_of_withHash`: the adversary, then the batching over `π`, is the adversary's run
  with its transcript recorded, then the batching with the two calls, the transcript forgotten
  (`logged_run_forget`); past `2^128` adversary queries the bound exceeds `1`
  (`one_le_batchingBound`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Compile.Rom
open Common (RandomPermutationOracles OracleQueryLog PermutationEdges queryPermutation
  loggedOracles lazyRandomPermutationOracles runWithRandomPermutation)

/-- **The adversary run with its permutation queries recorded, the record forgotten**, is its run
against the lazy permutation. -/
theorem logged_run_forget {α : Type} (A : OracleComp RandomPermutationOracles α) :
    ∀ (E : PermutationEdges KeccakState) (T : PermutationTranscript),
      (fun p : α × (PermutationEdges KeccakState × PermutationTranscript) ↦ (p.1, p.2.1)) <$>
        (simulateQ loggedRandomPermutationOracles A).run (E, T) =
      (simulateQ lazyRandomPermutationOracles A).run E := by
  induction A using OracleComp.inductionOn with
  | pure x => intro E T; simp
  | query_bind t k ih =>
    intro E T
    rcases t with n | q
    · simp [loggedRandomPermutationOracles, lazyRandomPermutationOracles, ih]
    · simp [loggedRandomPermutationOracles, lazyRandomPermutationOracles, ih]

namespace Guest

namespace Batch

theorem runBatching_eq_withHash {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (prog : VerifierProgram Bool) (proof : Proof) :
    runBatching F prog proof = runBatchingWithHash (keccak256With F) F prog proof := by
  simp only [runBatching, runBatchingWithHash, runProof_eq_withHash]

theorem simulateQ_runBatchingWithHash {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) (prog : VerifierProgram Bool) (proof : Proof) :
    simulateQ impl (runBatchingWithHash callKeccak256 callKeccakF1600 prog proof) =
      runBatchingWithHash (implH impl) (implF impl) prog proof := by
  simp only [runBatchingWithHash, simulateQ_bind, simulateQ_queryH, simulateQ_queryF,
    simulateQ_runProof]

/-- **The batching game over `π`** is the adversary's run with its transcript recorded, then the
batching with the two calls, the transcript forgotten. -/
theorem batchingGame_eq_withHash (A : OracleComp RandomPermutationOracles (Unit × Proof))
    (prog : VerifierProgram Bool) :
    runWithRandomPermutation (do
        let z ← A
        let accepted ← runBatching queryPermutation prog z.2
        return (z, accepted)) =
      Prod.fst <$> Rpm.runAdversaryThen A fun z ↦
        runBatchingWithHash callKeccak256 callKeccakF1600 prog z.2 := by
  have hB : ∀ proof : Proof,
      simulateQ lazyRandomPermutationOracles (runBatching queryPermutation prog proof) =
        simulateQ keccakCallsOverRandomPermutation
          (runBatchingWithHash callKeccak256 callKeccakF1600 prog proof) := by
    intro proof
    have e : runBatching queryPermutation prog proof = simulateQ keccakCallsOverQueryPermutation
        (runBatchingWithHash callKeccak256 callKeccakF1600 prog proof) := by
      rw [runBatching_eq_withHash, simulateQ_runBatchingWithHash]; rfl
    rw [e, simulateQ_lazy_keccakCallsOverQueryPermutation]
  have hA : (simulateQ lazyRandomPermutationOracles A).run [] =
      (fun p ↦ (p.1, p.2.1)) <$> (simulateQ loggedRandomPermutationOracles A).run ([], []) :=
    (logged_run_forget A [] []).symm
  simp only [runWithRandomPermutation, Rpm.runAdversaryThen, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, hA, bind_map_left, hB]

/-- Past `2^128` adversary queries the bound of `BatchingSound` exceeds `1`: its first term alone
is above `2^128 · 8 · 2^-130 = 2`. -/
theorem one_le_batchingBound {QA QV M : ℕ} (hQA : 2 ^ 128 < QA) :
    1 ≤ (((QA + QV : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130 +
      5 * ((QA + QV : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  refine le_add_right ?_
  have h : (2 : ℝ≥0∞) ^ 130 ≤ (((QA + QV : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) := by
    have : 2 ^ 130 ≤ (QA + QV + 1) * max (2 * M - 3) 8 :=
      calc 2 ^ 130 ≤ 2 ^ 128 * 8 := by norm_num
        _ ≤ (QA + QV + 1) * 8 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := Nat.mul_le_mul_left _ (le_max_right _ _)
    exact_mod_cast this
  rw [ENNReal.inv_pow]
  calc (1 : ℝ≥0∞) = 2 ^ 130 * (2 ^ 130)⁻¹ := (ENNReal.mul_inv_cancel (by simp) (by simp)).symm
    _ ≤ _ := by gcongr

/-- **`BatchingSound`, from the experiment with the two calls.** -/
theorem batchingSound_of_withHash (h : BatchingSoundWithHash) : BatchingSound := by
  intro M bytecode hb hM A QA hA hQV
  rcases le_or_gt QA (2 ^ 128) with hQA | hQA
  · rw [batchingGame_eq_withHash, prEvent_map]
    exact h M bytecode hb hM A QA hA hQA hQV
  · exact prEvent_le_of_one_le _ (one_le_batchingBound hQA)

end Batch

namespace Budget

/-- The honest proof over the deployed Keccak-f[1600] is the two-call prover's with the deployed
Keccak-256 and Keccak-f[1600]. -/
theorem honestProofWithDeployedKeccak_eq_withHash (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) :
    leanVmHonestProver (m := Id) keccakF1600 prog input t ρ fuel =
      honestProofWithDeployedKeccakWithHash proverWithHash prog input t ρ fuel := by
  simp only [honestProofWithDeployedKeccakWithHash, leanVmHonestProver,
    Prover.prove_eq_withHash, proverWithHash, simulateQ_proveWithHash]
  have h1 : implH deployedKeccakCalls = keccak256With (m := Id) keccakF1600 := by funext x; rfl
  have h2 : implF deployedKeccakCalls = keccakF1600 := by funext x; rfl
  rw [h1, h2]
  rfl

end Budget

end Guest

end LeanVM

end
