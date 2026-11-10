/-
  LeanVM.Prover.CompleteChild

  The guest's completeness end statement for any honest prover that is the specification's honest
  prover at a child's witness: `LeanVM.Guest.Completeness.GuestChildComplete` with that prover.
-/

import LeanVM.Prover.Complete
import LeanVM.Guest.Child.NZRpm
import LeanVM.Guest.Child.Deployed
import LeanVM.Guest.WithHash

/-!
# The guest's completeness for a prover that is the specification at a child's witness

* `guestChildComplete_of_spec`: if on every valid execution within the cap, at a valid rate, `A`
  is the specification at a child's witness (`SpecOnValid A ChildFor`), and everywhere it is the
  specification at a child's witness or makes no proof (`ChildSpec`), then both parts of
  `LeanVM.Guest.Completeness.GuestChildComplete` hold for `A` (`rpmChild_at`, `rpmChild_le`,
  `childOk_of_verifierRZ_of`). No proof is a rejection here too: the verifier refusing a zero
  challenge rejects the empty proof (`verifierRefusingZeroWithHash_empty`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakHash LeanVM.Guest.Child LeanVM.Node
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)
open scoped ENNReal

section Empty

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
  (F : KeccakState → m KeccakState)

/-- **The verifier refusing a zero challenge rejects the empty proof**, once it has its seed. -/
theorem verifierRefusingZeroWithHash_empty (prog : LeanIsaProgram) (input : PublicInput) :
    Guest.Budget.verifierRefusingZeroWithHash H F prog input ⟨[], []⟩ =
      seedWithHash H F (bytecodeWords prog) (publicInputDigest input) >>= fun _ ↦ pure false := by
  obtain ⟨k, hk⟩ := leanVmProgram_read (bytecodeWords prog) (publicInputDigest input)
  simp only [Guest.Budget.verifierRefusingZeroWithHash, hk, VerifierProgram.refusingZeroChallenge,
    runProof_read_empty]

end Empty

/-- **Both parts of `GuestChildComplete`, for a prover that is the specification at a child's
witness**: on valid executions within the cap at a valid rate (`SpecOnValid A ChildFor`), and
everywhere the specification at a child's witness or no proof (`ChildSpec`). -/
theorem guestChildComplete_of_spec (A : HonestProverWithHash) (hA : SpecOnValid A ChildFor)
    (hA' : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ),
      ChildSpec A prog input t ρ fuel) :
    (∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← (simulateQ LeanVM.keccakCallsOverRandomPermutation (do
          match ← A prog input t ρ (2 ^ 33) with
          | none => pure false
          | some proof =>
            Guest.Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input
              proof)).run' []}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 126) ∧
    ∀ (s : NodeStatement) (t : Execution Guest.guestProgram) (ρ : ℕ), 2 ^ 21 < t.committedSize →
      s.deferredClaim.HasBytecodeShape (bytecodeWords Guest.guestProgram) →
      let input := PublicInput.ofDigest (statementDigest (deployedSeed Guest.guestProgram) s)
      ∀ proof, Guest.Budget.honestProofWithDeployedKeccakWithHash A Guest.guestProgram input t ρ
          (2 ^ 33) = some proof →
      Guest.Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 Guest.guestProgram input
          proof = true →
      ∃ fresh, fresh.Holds (bytecodeWords Guest.guestProgram) ∧
        LeanVM.Guest.AcceptableChild (bytecodeWords Guest.guestProgram)
          (deployedSeed Guest.guestProgram) ⟨s, fresh, proof⟩ := by
  refine ⟨fun prog input t ρ hv hbudget hρ ↦ ?_, fun s t ρ h21 hsh _ hsome hacc ↦
    childOk_of_verifierRZ_of (hA' _ _ _ _ _) h21 hsh hsome hacc⟩
  obtain ⟨w, s, hw, hAw⟩ := hA prog input t ρ (2 ^ 33) hv hbudget hρ
  refine le_of_eq_of_le ((noProof_evalDistEq LeanVM.keccakCallsOverRandomPermutation _ _ _
    (verifierRefusingZeroWithHash_empty _ _ prog input) []).prEvent_eq (· = false)) ?_
  rw [hAw, ← honestComp_eq_getD]
  exact (rpmChild_at hw.1 (by norm_num)).trans rpmChild_le

end LeanVM.Prover
