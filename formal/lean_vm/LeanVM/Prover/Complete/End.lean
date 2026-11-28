/-
  LeanVM.Prover.Complete.End

  `LeanVM.Completeness` from three facts about the honest prover: its witness exists, its script
  wins the verifier's program, and its queries are bounded.
-/

module

public import LeanVM.Prover.Complete.Rpm
public import LeanVM.Prover.Complete.Numbers
public import LeanVM.Protocol.ExperimentBridge
import LeanVM.Protocol.WithHashBridge

/-!
# Completeness from the honest script

The statement's prover `LeanVM.Prover.prove` computes the witness (`witness?`) and runs the honest
script (`honestScript`) against the verifier's own program. Completeness follows from three
facts about it, each stated here as a proposition:

* `WitnessExists`: on every execution `LeanVM.Completeness` admits there is a witness;
* `HonestWins`: there the honest script wins the verifier's program (`Wins`, with proofs of work
  of at most `17` bits) with `true`;
* `HonestCosts`: there the honest prover from leanVM's seed makes at most `QA` queries, the
  verifier at most `QV` on any proof, with `QA + QV ≤ 2^120`, and the two together at most
  `N ≤ 2^125` permutation calls.

`completenessWithHash_of`: these give `CompletenessWithHash`, through the random-permutation bound
(`rpmComplete`) and the numbers (`completenessBound_le`); no proof is a rejection, as the empty
proof's is (`noProof_evalDistEq`, restored). `completeness_of_withHash` (restored): the statement's
experiment is the two-call one.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.Verifier LeanVM.Rpm
open OracleComp OracleSpec
open scoped ENNReal

/-! ## No proof is a rejection -/

section Empty

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
  (F : KeccakState → m KeccakState)

/-- **No program reading first accepts the empty proof**: it rejects, with no call. -/
theorem runProof_read_empty (k : E → VerifierProgram Bool) (sd : KeccakState) :
    runProofWithHash H F (VerifierProgram.read k) sd ⟨[], []⟩ = pure false := by
  simp only [runProofWithHash, runWithHash, pure_bind]

/-- The verifier's program reads first. -/
theorem leanVmProgram_read (bytecode : List K) (publicInput : Digest) :
    ∃ k, leanVmVerifierProgram bytecode publicInput = VerifierProgram.read k :=
  ⟨_, rfl⟩

/-- **The verifier rejects the empty proof**, once it has its seed. -/
theorem verifierWithHash_empty (prog : LeanIsaProgram) (input : PublicInput) :
    verifierWithHash H F prog input ⟨[], []⟩ =
      seedWithHash H F (bytecodeWords prog) (publicInputDigest input) >>= fun _ ↦ pure false := by
  obtain ⟨k, hk⟩ := leanVmProgram_read (bytecodeWords prog) (publicInputDigest input)
  simp only [verifierWithHash, verifyWithHash, hk, runProof_read_empty]

end Empty

/-- **No proof is a rejection**: where the verifier `V` rejects the empty proof after some calls
`Y`, the experiment that fails when the prover `X` makes no proof is, in distribution, the one
that runs `V` on the empty proof instead, against any stateful implementation of the calls. -/
theorem noProof_evalDistEq {σ α : Type} (impl : QueryImpl KeccakCalls (StateT σ ProbComp))
    (X : OracleComp KeccakCalls (Option Proof)) (V : Proof → OracleComp KeccakCalls Bool)
    (Y : OracleComp KeccakCalls α) (hV : V ⟨[], []⟩ = Y >>= fun _ ↦ pure false) (s : σ) :
    (simulateQ impl (do
      match ← X with
      | none => pure false
      | some proof => V proof)).run' s =ᵈ
      (simulateQ impl ((·.getD ⟨[], []⟩) <$> X >>= V)).run' s := by
  rw [bind_map_left]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine EvalDistEq.bind_right _ fun ⟨r, s'⟩ ↦ ?_
  cases r with
  | none =>
    simp only [Option.getD_none, hV, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, map_bind, map_pure]
    refine EvalDistEq.of_evalDist_eq ?_
    rw [OracleComp.evalDist_bind_const]
  | some p => exact EvalDistEq.rfl

/-! ## The three facts -/

/-- **The witness exists** on every execution `LeanVM.Completeness` admits. -/
def WitnessExists : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 30 → t.pointerWidth ≤ maxPointerWidth →
    t.KeccakBlocksInWindows → ∃ W, witness? prog input t = some W

/-- **The honest script wins** the verifier's program with `true`, its proofs of work of at most
`17` bits, on every execution `LeanVM.Completeness` admits and its witness. -/
def HonestWins : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ) (W : Witness),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 30 → t.pointerWidth ≤ maxPointerWidth →
    t.KeccakBlocksInWindows → 1 ≤ ρ ∧ ρ ≤ 4 → witness? prog input t = some W →
    Wins 17 (fun a _ _ _ ↦ a = true)
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (honestScript W ρ (publicInputDigest input)) false []

/-- **The honest prover's queries are bounded**: from leanVM's seed at `2^35` nonces per proof of
work, at most `QA` queries of the prover and `QV` of the verifier on any proof, `QA + QV ≤ 2^120`,
and at most `N ≤ 2^125` permutation calls of the prover then the verifier. -/
def HonestCosts : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ) (W : Witness),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 30 → t.pointerWidth ≤ maxPointerWidth →
    t.KeccakBlocksInWindows → 1 ≤ ρ ∧ ρ ≤ 4 → witness? prog input t = some W →
    ∃ QA QV N : ℕ, QA + QV ≤ 2 ^ 120 ∧ N ≤ 2 ^ 125 ∧
      IsTotalQueryBound (honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestScript W ρ (publicInputDigest input)) (2 ^ 35)) QA ∧
      (∀ π, IsTotalQueryBound (verifierComp (leanVmSeed (bytecodeWords prog)
        (publicInputDigest input)) (leanVmVerifierProgram (bytecodeWords prog)
          (publicInputDigest input)) π) QV) ∧
      Common.QueryCostAtMost (honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestScript W ρ (publicInputDigest input)) (2 ^ 35) >>= fun π ↦
          verifyWithHash callKeccak256 callKeccakF1600 (bytecodeWords prog)
            (publicInputDigest input) π) hashBlocks N

/-! ## Completeness -/

/-- The honest prover with the two calls, made total by the empty proof, is the random-oracle
model's honest prover from leanVM's seed. -/
theorem getD_proverWithHash {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (fuel : ℕ) :
    (·.getD ⟨[], []⟩) <$> proverWithHash prog input t ρ fuel =
      honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestScript W ρ (publicInputDigest input)) fuel := by
  simp only [proverWithHash, proveWithHash, hW, hρ, and_self, ↓reduceIte, honestComp,
    seedRun_leanVmSeed, map_bind, bind_pure_comp]

/-- **Completeness from the three facts**, in the experiment with the two calls. -/
theorem completenessWithHash_of (hex : WitnessExists) (hwin : HonestWins) (hcost : HonestCosts) :
    CompletenessWithHash := by
  intro prog input t ρ hv hs hpw hk hρ
  obtain ⟨W, hW⟩ := hex prog input t hv hs hpw hk
  obtain ⟨QA, QV, N, hQ, hN, hA, hV, hcN⟩ := hcost prog input t ρ W hv hs hpw hk hρ hW
  have hw := hwin prog input t ρ W hv hs hpw hk hρ hW
  refine le_of_eq_of_le ((noProof_evalDistEq keccakCallsOverRandomPermutation _ _ _
    (verifierWithHash_empty _ _ prog input) []).prEvent_eq (· = false)) ?_
  rw [getD_proverWithHash hW hρ]
  exact (rpmComplete (bytecodeWords prog) (publicInputDigest input) _ (by norm_num) (by norm_num)
    (by norm_num) hw hA hV hcN).trans (completenessBound_le hQ hN)

/-! ## The statement's experiment -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- The two-call prover commutes with simulation. -/
theorem simulateQ_proveWithHash (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) :
    simulateQ impl (proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel) =
      proveWithHash (implH impl) (implF impl) prog input t ρ fuel := by
  simp only [proveWithHash]
  split
  · simp
  · split
    · simp only [simulateQ_bind, simulateQ_seedWith, simulateQ_runScript]
    · simp

end Commute

theorem prover_queryPermutation (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) :
    prove Common.queryPermutation prog input t ρ fuel =
      simulateQ keccakCallsOverQueryPermutation (proverWithHash prog input t ρ fuel) := by
  have hH : implH keccakCallsOverQueryPermutation = keccak256With Common.queryPermutation :=
    funext fun _ ↦ by simp only [implH, keccakCallsOverQueryPermutation]
  have hF : implF keccakCallsOverQueryPermutation = Common.queryPermutation :=
    funext fun _ ↦ by simp only [implF, keccakCallsOverQueryPermutation]
  rw [prove_eq_withHash, proverWithHash, simulateQ_proveWithHash, hH, hF]

end LeanVM.Prover

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover LeanVM.Protocol.Compile OracleComp OracleSpec
open Common (runWithRandomPermutation)

theorem completenessExperiment_eq_withHash (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) :
    completenessExperiment prog input t ρ fuel =
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
  intro prog input t ρ hv hs hpw hk hρ
  rw [completenessExperiment_eq_withHash]
  exact h prog input t ρ hv hs hpw hk hρ

/-- **Completeness from the three facts about the honest prover.** -/
theorem completeness_of (hex : WitnessExists) (hwin : HonestWins) (hcost : HonestCosts) :
    Completeness :=
  completeness_of_withHash (completenessWithHash_of hex hwin hcost)

end LeanVM

end
