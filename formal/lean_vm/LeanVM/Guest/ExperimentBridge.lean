module

public import LeanVM.Protocol.ExperimentBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.AcceptableChild

@[expose] public section

/-!
# The guest's statements over `π` are the statements with the two calls

The statement's batching run and verifier refusing a zero challenge are over a permutation alone;
with the hash Keccak-256 over it they are the forms with a hash (`runBatching_eq_withHash`,
`verifierRefusingZero_eq_withHash`). The statement's experiments are games in the model's oracles;
the proofs' run the two calls against the model (`LeanVM.Protocol.ExperimentBridge`):

* `guestChildComplete_of_withHash`: the honest prover's proof, then the check, over `π` is the
  two-call run, and with the deployed Keccak-f[1600] the deployed Keccak's;
* `batchingSound_of_withHash`: the adversary, then the batching over `π`, is the adversary's run
  with its transcript recorded, then the batching with the two calls, the transcript forgotten
  (`logged_run_forget`).
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

/-- **`BatchingSound`, from the experiment with the two calls.** -/
theorem batchingSound_of_withHash (h : BatchingSoundWithHash) : BatchingSound := by
  intro M bytecode hb hM A QA hA hQA hQV
  rw [batchingGame_eq_withHash, prEvent_map]
  exact h M bytecode hb hM A QA hA hQA hQV

end Batch

namespace Budget

open LeanVM.Guest.Completeness

theorem verifierRefusingZero_eq_withHash {m : Type → Type} [Monad m]
    (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    verifierRefusingZero F prog input proof =
      verifierRefusingZeroWithHash (keccak256With F) F prog input proof := by
  simp only
    [verifierRefusingZero, verifierRefusingZeroWithHash, seedWith_eq_withHash, runProof_eq_withHash]

theorem simulateQ_verifierRefusingZeroWithHash {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    simulateQ impl (verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof) =
      verifierRefusingZeroWithHash (implH impl) (implF impl) prog input proof := by
  simp only [verifierRefusingZeroWithHash, simulateQ_bind, Prover.simulateQ_seedWith,
    simulateQ_runProof]

/-- The honest proof over the deployed Keccak-f[1600] is the two-call prover's with the deployed
Keccak-256 and Keccak-f[1600]. -/
theorem honestProofWithDeployedKeccak_eq_withHash (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) :
    honestProofWithDeployedKeccak leanVmHonestProver prog input t ρ fuel =
      honestProofWithDeployedKeccakWithHash proverWithHash prog input t ρ fuel := by
  simp only [honestProofWithDeployedKeccak, honestProofWithDeployedKeccakWithHash,
      leanVmHonestProver,
    Prover.prove_eq_withHash, proverWithHash, simulateQ_proveWithHash]
  have h1 : implH deployedKeccakCalls = keccak256With (m := Id) keccakF1600 := by funext x; rfl
  have h2 : implF deployedKeccakCalls = keccakF1600 := by funext x; rfl
  rw [h1, h2]
  rfl

/-- **`GuestChildComplete`, from the statement with the two calls.** -/
theorem guestChildComplete_of_withHash (h : GuestChildCompleteWithHash) : GuestChildComplete := by
  refine ⟨fun prog input t ρ hv hs hρ ↦ ?_, fun s t ρ hshape ↦ ?_⟩
  · convert h.1 prog input t ρ hv hs hρ using 3
    rw [← simulateQ_lazy_keccakCallsOverQueryPermutation]
    simp only [runWithRandomPermutation, prover_queryPermutation, simulateQ_bind]
    congr 2
    funext x
    cases x
    · simp only [simulateQ_pure]
    · simp only [simulateQ_verifierRefusingZeroWithHash, verifierRefusingZero_eq_withHash]
      rfl
  · intro input proof hsome hacc
    have key := h.2 s t ρ hshape
    simp only at key
    rw [honestProofWithDeployedKeccak_eq_withHash] at hsome
    rw [verifierRefusingZero_eq_withHash] at hacc
    exact key proof hsome hacc

end Budget

end Guest

end LeanVM

end
