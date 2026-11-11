/-
  LeanVM.Prover.Complete

  The completeness end statements for any honest prover that is the specification's honest
  prover at some witness: `LeanVM.Completeness` and `LeanVM.Guest.Completeness.GuestChildComplete` with
  that prover.
-/

import LeanVM.Protocol.LeanVMRpm
import LeanVM.Guest.Child.NZRpm
import LeanVM.Guest.Child.Deployed
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash

/-!
# Completeness for a prover that is the specification at a witness

The completeness theorems (`LeanVM.completeness_holds`, `LeanVM.Guest.Budget.guest_child_complete`)
are proved for provers that choose a witness classically (`honestComp`, `childComp`). Their
proofs need of the prover only that, on the executions they speak of, it is the specification's
honest prover (`Rom.honestComp?` at leanVM's seed and program, with the strategy
`leanVmProver prog s ρ (stackOf prog s w)`) at some witness `w` at sizes `s` that is honest
(`HonestFor`), or a child's (`ChildFor`). Here they are restated for any such prover `A`:

* `completeness_of_spec`: if on every valid execution within the cap, at a valid rate, `A` is the
  specification at an honest witness, then the body of `LeanVM.Completeness` holds for `A`, with
  the same bound `2^-256` (`completenessRpm_at`, `completenessRpm_le`);
* `guestChildComplete_of_spec`: if moreover the witness is a child's, and everywhere `A` is the
  specification at a child's witness or makes no proof (`ChildSpec`), then both parts of
  `LeanVM.Guest.Completeness.GuestChildComplete` hold for `A`, with the same bound `2^-126`
  (`rpmChild_at`, `rpmChild_le`, `childOk_of_verifierRZ_of`).

The prover may make no proof (`none`); the experiments count that a rejection. The verifier
rejects the empty proof too, once it has its seed (`verifierWithHash_empty`,
`verifierRefusingZeroWithHash_empty`), so in distribution an experiment is the one with the empty
proof in place of `none` (`noProof_evalDistEq`), and with it `Rom.honestComp?` is
`Rom.honestComp` (`honestComp_eq_getD`), where the theorems of the random-permutation model
apply.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakHash LeanVM.Guest.Child LeanVM.Node
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)
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

/-- **The verifier refusing a zero challenge rejects the empty proof**, once it has its seed. -/
theorem verifierRefusingZeroWithHash_empty (prog : LeanIsaProgram) (input : PublicInput) :
    Guest.Budget.verifierRefusingZeroWithHash H F prog input ⟨[], []⟩ =
      seedWithHash H F (bytecodeWords prog) (publicInputDigest input) >>= fun _ ↦ pure false := by
  obtain ⟨k, hk⟩ := leanVmProgram_read (bytecodeWords prog) (publicInputDigest input)
  simp only [Guest.Budget.verifierRefusingZeroWithHash, hk, VerifierProgram.refusingZeroChallenge,
    runProof_read_empty]

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

/-- **The prover is the specification at an honest witness** on every valid execution within the
verifier's cap, at a valid rate. -/
def SpecOnValid (A : HonestProverWithHash)
    (W : (prog : LeanIsaProgram) → PublicInput → (t : Execution prog) → ℕ →
      EnsembleWitness (leanIsaEnsemble prog t.logMemorySize) → Sizes → Prop) : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 32 → 1 ≤ ρ ∧ ρ ≤ 4 →
    ∃ w s, W prog input t ρ w s ∧
      A prog input t ρ fuel = Rom.honestComp? (leanVmSeed (bytecodeWords prog) (publicInputDigest
          input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (leanVmProver prog s ρ (stackOf prog s w)) fuel

/-- **Completeness for a prover that is the specification at an honest witness**: the body of
`LeanVM.Completeness` for `A`. No proof is a rejection, as the empty proof's is
(`noProof_evalDistEq`). -/
theorem completeness_of_spec (A : HonestProverWithHash) (hA : SpecOnValid A HonestFor) :
    ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 32 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← verifierCompletenessExperimentWithHash A prog input t ρ (2 ^ 25)}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  intro prog input t ρ hv hbudget hρ
  obtain ⟨w, s, hw, hAw⟩ := hA prog input t ρ (2 ^ 25) hv hbudget hρ
  refine le_of_eq_of_le ((noProof_evalDistEq keccakCallsOverRandomPermutation _ _ _
    (verifierWithHash_empty _ _ prog input) []).prEvent_eq (· = false)) ?_
  rw [hAw, ← honestComp_eq_getD]
  exact (Rpm.completenessRpm_at hw (by norm_num)).trans Rpm.completenessRpm_le

/-- **Both parts of `GuestChildComplete`, for a prover that is the specification at a child's
witness**: on valid executions within the cap at a valid rate (`SpecOnValid A ChildFor`), and
everywhere the specification at a child's witness or no proof (`ChildSpec`). -/
theorem guestChildComplete_of_spec (A : HonestProverWithHash) (hA : SpecOnValid A ChildFor)
    (hA' : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ),
      ChildSpec A prog input t ρ fuel) :
    (∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 32 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← (simulateQ LeanVM.keccakCallsOverRandomPermutation (do
          match ← A prog input t ρ (2 ^ 25) with
          | none => pure false
          | some proof =>
            Guest.Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input
              proof)).run' []}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 126) ∧
    ∀ (s : NodeStatement) (t : Execution Guest.guestProgram) (ρ : ℕ),
      s.deferredClaim.HasBytecodeShape (bytecodeWords Guest.guestProgram) →
      let input := PublicInput.ofDigest (statementDigest (deployedSeed Guest.guestProgram) s)
      ∀ proof, Guest.Budget.honestProofWithDeployedKeccakWithHash A Guest.guestProgram input t ρ
          (2 ^ 25) = some proof →
      Guest.Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 Guest.guestProgram input
          proof = true →
      ∃ fresh, fresh.Holds (bytecodeWords Guest.guestProgram) ∧
        LeanVM.Guest.AcceptableChild (bytecodeWords Guest.guestProgram)
          (deployedSeed Guest.guestProgram) ⟨s, fresh, proof⟩ := by
  refine ⟨fun prog input t ρ hv hbudget hρ ↦ ?_, fun s t ρ hsh _ hsome hacc ↦
    childOk_of_verifierRZ_of (hA' _ _ _ _ _) hsh hsome hacc⟩
  obtain ⟨w, s, hw, hAw⟩ := hA prog input t ρ (2 ^ 25) hv hbudget hρ
  refine le_of_eq_of_le ((noProof_evalDistEq LeanVM.keccakCallsOverRandomPermutation _ _ _
    (verifierRefusingZeroWithHash_empty _ _ prog input) []).prEvent_eq (· = false)) ?_
  rw [hAw, ← honestComp_eq_getD]
  exact (rpmChild_at hw.1 (by norm_num)).trans rpmChild_le

end LeanVM.Prover
