import LeanVM.Protocol.WithHashBridge
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Prover.Refine
import Common.PiOnly

/-!
# The statement's experiments are the experiments with the two calls

The statement's experiments are games in the model's oracles (coins, `π`, `π⁻¹`), the verifier and
the prover over `π` (`Common.queryPermutation`), run against the lazily sampled permutation; the
proofs' are the experiments in which Keccak-256 and Keccak-f[1600] are two calls answered by the
model (`keccakCallsOverRandomPermutation`), after the adversary's run with its permutation queries
recorded (`Rpm.runAdversaryThen`).

* `keccakCallsOverQueryPermutation`: the two calls answered over `π` in the model's oracles; the
  verifier and the prover over `π` are the two-call ones so answered (`verifier_queryPermutation`,
  `prover_queryPermutation`), and the lazy permutation after it answers the two calls as the model
  does (`lazy_comp_keccakCallsOverQueryPermutation`).
* `logged_run`: the adversary run with its queries recorded (`Common.loggedOracles`), then against
  the lazy permutation, is its run with its permutation queries recorded, the coins left out.
* `map_soundnessExperiment`: so the statement's soundness experiment, its transcript's coins left
  out, is the two-call experiment; `knowledgeSoundness_of_withHash` and
  `completeness_of_withHash` give the end statements from the two-call ones.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Compile.Rom
open Common (RandomPermutationOracles OracleQueryLog PermutationEdges queryPermutation
  loggedOracles lazyRandomPermutationOracles runWithRandomPermutation)

/-! ## The two calls over `π` -/

/-- **The two calls answered over `π`** in the model's oracles: Keccak-256 the sponge over `π`,
Keccak-f[1600] `π`. -/
def keccakCallsOverQueryPermutation : QueryImpl KeccakCalls (OracleComp RandomPermutationOracles)
  | .inl x => keccak256With queryPermutation x
  | .inr s => queryPermutation s

/-- The lazy permutation after the two calls over `π` answers them as the model does. -/
theorem lazy_comp_keccakCallsOverQueryPermutation :
    lazyRandomPermutationOracles ∘ₛ keccakCallsOverQueryPermutation =
      keccakCallsOverRandomPermutation := by
  funext t
  rcases t with x | s
  · show simulateQ lazyRandomPermutationOracles (keccak256With queryPermutation x) =
      keccak256With lazyPermutationForward x
    rw [Common.simulateQ_keccak256With]
    congr 1
    funext s
    simp only [queryPermutation, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, keccakCallsOverQueryPermutation, queryPermutation,
      simulateQ_spec_query]
    rfl

/-- A computation over the two calls over `π`, run against the lazy permutation, is its run with the
model's answers. -/
theorem simulateQ_lazy_keccakCallsOverQueryPermutation {α : Type} (oa : OracleComp KeccakCalls α) :
    simulateQ lazyRandomPermutationOracles (simulateQ keccakCallsOverQueryPermutation oa) =
      simulateQ keccakCallsOverRandomPermutation oa := by
  rw [← QueryImpl.simulateQ_compose, lazy_comp_keccakCallsOverQueryPermutation]

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- The two-call verifier commutes with simulation. -/
theorem simulateQ_verifierWithHash (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    simulateQ impl (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) =
      verifierWithHash (implH impl) (implF impl) prog input proof := by
  simp only [verifierWithHash, verifyWithHash, simulateQ_bind, Prover.simulateQ_seedWith,
    simulateQ_runProof]

/-- The two-call prover commutes with simulation. -/
theorem simulateQ_proveWithHash (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) :
    simulateQ impl (Prover.proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel) =
      Prover.proveWithHash (implH impl) (implF impl) prog input t ρ fuel := by
  simp only [Prover.proveWithHash]
  split
  · simp
  · split
    · exact Prover.simulateQ_seedRunScript impl _ _ _ _ _
    · simp

end Commute

theorem verifier_queryPermutation (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    leanVmVerifier queryPermutation prog input proof =
      simulateQ keccakCallsOverQueryPermutation
        (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) := by
  rw [verifier_eq_withHash, simulateQ_verifierWithHash]; rfl

theorem prover_queryPermutation (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) :
    leanVmHonestProver queryPermutation prog input t ρ fuel =
      simulateQ keccakCallsOverQueryPermutation (proverWithHash prog input t ρ fuel) := by
  rw [leanVmHonestProver, Prover.prove_eq_withHash, proverWithHash, simulateQ_proveWithHash]; rfl

/-! ## The adversary's transcript -/

theorem permutationQueries_nil : permutationQueries [] = [] := rfl

theorem permutationQueries_append_coin (log : OracleQueryLog) (n : ℕ) (u : Fin (n + 1)) :
    permutationQueries (log ++ [⟨.inl n, u⟩]) = permutationQueries log := by
  simp [permutationQueries, List.filterMap_append]

theorem permutationQueries_append_query (log : OracleQueryLog)
    (q : Common.PermutationQuery KeccakState)
    (y : KeccakState) :
    permutationQueries (log ++ [⟨.inr q, y⟩]) = permutationQueries log ++ [(q, y)] := by
  simp [permutationQueries, List.filterMap_append]

/-- **The adversary run with its queries recorded, then against the lazy permutation**, is its run
with its permutation queries recorded: the coins are left out of the transcript. -/
theorem logged_run {α : Type} (A : OracleComp RandomPermutationOracles α) :
    ∀ (log₀ : OracleQueryLog) (E : PermutationEdges KeccakState),
      (fun p : (α × OracleQueryLog) × PermutationEdges KeccakState ↦
          (p.1.1, p.2, permutationQueries p.1.2)) <$>
        (simulateQ lazyRandomPermutationOracles ((simulateQ loggedOracles A).run log₀)).run E =
      (fun p : α × (PermutationEdges KeccakState × PermutationTranscript) ↦ (p.1, p.2.1, p.2.2)) <$>
        (simulateQ loggedRandomPermutationOracles A).run (E, permutationQueries log₀) := by
  induction A using OracleComp.inductionOn with
  | pure x => intro log₀ E; simp
  | query_bind t k ih =>
    intro log₀ E
    rcases t with n | q
    · simp [loggedOracles, loggedRandomPermutationOracles, lazyRandomPermutationOracles,
        permutationQueries_append_coin, ih]
    · simp [loggedOracles, loggedRandomPermutationOracles, lazyRandomPermutationOracles,
        permutationQueries_append_query, ih]

/-! ## Knowledge soundness -/

/-- **The statement's soundness experiment, its transcript's coins left out, is the two-call
experiment.** -/
theorem map_soundnessExperiment (A : RandomPermutationAdversary) :
    (fun z : ExperimentOutcome ↦
        ((((z.program, z.input), z.proof), z.accepted), permutationQueries z.transcript)) <$>
      knowledgeSoundnessExperiment A =
      soundnessExperimentWithHash A := by
  have hA : (simulateQ loggedRandomPermutationOracles A).run ([], []) =
      (fun p : ((ProgramAndInput × Proof) × OracleQueryLog) × PermutationEdges KeccakState ↦
          (p.1.1, p.2, permutationQueries p.1.2)) <$>
        (simulateQ lazyRandomPermutationOracles ((simulateQ loggedOracles A).run [])).run [] := by
    rw [logged_run A [] []]
    simp [permutationQueries_nil]
  have hV : ∀ (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof),
      simulateQ lazyRandomPermutationOracles (leanVmVerifier queryPermutation prog input proof) =
        simulateQ keccakCallsOverRandomPermutation
          (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) := by
    intro prog input proof
    rw [verifier_queryPermutation, simulateQ_lazy_keccakCallsOverQueryPermutation]
  simp only [knowledgeSoundnessExperiment, soundnessExperimentWithHash, Rpm.runAdversaryThen,
    runWithRandomPermutation, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure, map_bind, map_pure, hA, bind_map_left, hV]

/-- **Knowledge soundness, from the two-call experiment.** -/
theorem knowledgeSoundness_of_withHash (h : KnowledgeSoundnessWithHash) :
    KnowledgeSoundness transcriptExtractor := by
  intro A Q hQ hcap
  have := h A Q hQ hcap
  rw [← map_soundnessExperiment, prEvent_map] at this
  exact this

/-! ## Completeness -/

theorem verifierCompletenessExperiment_eq_withHash (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) :
    completenessExperiment leanVmHonestProver prog input t ρ fuel =
      verifierCompletenessExperimentWithHash proverWithHash prog input t ρ fuel := by
  simp only [completenessExperiment, verifierCompletenessExperimentWithHash,
    runWithRandomPermutation, prover_queryPermutation, verifier_queryPermutation]
  rw [← simulateQ_lazy_keccakCallsOverQueryPermutation, simulateQ_bind, simulateQ_bind]
  simp only [simulateQ_bind]
  congr 2
  funext x
  cases x <;> simp only [simulateQ_pure]

/-- **Completeness, from the two-call experiment.** -/
theorem completeness_of_withHash (h : CompletenessWithHash) : Completeness := by
  intro prog input t ρ hv hs hρ
  rw [verifierCompletenessExperiment_eq_withHash]
  exact h prog input t ρ hv hs hρ

end LeanVM
