/-
  LeanVM.Guest.Child.Honest

  The honest prover of a child: the compiled honest prover of a witness whose sizes are the
  execution's own, so that its stack is the execution's committed size. Its proof with the
  deployed Keccak is the pure prover's proof of that witness.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Rom
public import Statement.LeanVmGuest
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHash

/-!
# The honest prover of a child

A child's witness is an honest witness whose stacked size is the execution's committed size
(`ChildFor`; the specification witness is one within the cap, `LeanVM.Prover.childFor_trace`).
`Rom.honestComp?` is `Rom.honestComp` with `none` where it
makes no proof; a prover that is it at a child's witness or makes no proof (`ChildSpec`) has, with
Keccak-256 and Keccak-f[1600] (`honestProofWithDeployedKeccakWithHash`), the pure prover's proof
(`atKeccak_of_eq`, `prove_of_some`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.KeccakHash OracleComp OracleSpec
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The witness of a child's proof: an honest witness of the execution whose stacked size is the
execution's committed size. -/
def ChildFor (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)) (s : Sizes) : Prop :=
  HonestFor prog input t ρ w s ∧ (LeanIsa.blocks prog s).total = t.committedSize

/-- `deployedKeccakCalls` is the total implementation at Keccak-256 and Keccak-f[1600]. -/
theorem keccakImpl_eq : Budget.deployedKeccakCalls = totalImpl keccak256 keccakF1600 := by
  funext q
  rcases q with x | s <;> rfl

/-- The specification's honest prover of a child at a witness: `Rom.honestComp?` at leanVM's
seed, program and the witness's strategy, or no proof. -/
abbrev ChildSpec (A : HonestProverWithHash) (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) : Prop :=
  A prog input t ρ fuel = pure none ∨ ∃ w s, ChildFor prog input t ρ w s ∧
    A prog input t ρ fuel = Rom.honestComp? (leanVmSeed (bytecodeWords prog) (publicInputDigest
        input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (leanVmProver prog s ρ (stackOf prog s w)) fuel

/-- **A prover's proof with Keccak**, where it is the specification's honest prover of a
strategy: the pure prover's proof. -/
theorem atKeccak_of_eq {A : HonestProverWithHash} {prog : LeanIsaProgram} {input : PublicInput}
    {t : Execution prog} {ρ fuel : ℕ} {S : Strategy}
    (hA : A prog input t ρ fuel = Rom.honestComp? (leanVmSeed (bytecodeWords prog)
      (publicInputDigest input)) (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest
          input)) S fuel) :
    Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel =
      prove keccak256 keccakF1600 (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest
          input)) S
        (seed (bytecodeWords prog) (publicInputDigest input)) fuel := by
  unfold Budget.honestProofWithDeployedKeccakWithHash
  rw [hA]
  simp only [keccakImpl_eq, Rom.honestComp?, simulateQ_bind,
    simulateQ_proveM, implH_totalImpl, implF_totalImpl, seedRun_leanVmSeed]
  rw [← proveM_id]
  rfl

/-- **A proof with Keccak**, of a prover that is the specification at a child's witness or makes
no proof, is the pure prover's proof of a child's witness. -/
theorem prove_of_some {A : HonestProverWithHash} {prog : LeanIsaProgram} {input : PublicInput}
    {t : Execution prog} {ρ fuel : ℕ} (hA : ChildSpec A prog input t ρ fuel) {proof : Proof}
    (hsome : Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel = some proof) :
    ∃ w s, ChildFor prog input t ρ w s ∧
      prove keccak256 keccakF1600 (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest
          input))
        (leanVmProver prog s ρ (stackOf prog s w)) (seed (bytecodeWords prog) (publicInputDigest
            input))
        fuel = some proof := by
  rcases hA with hA | ⟨w, s, hc, hA⟩
  · unfold Budget.honestProofWithDeployedKeccakWithHash at hsome
    rw [hA, simulateQ_pure] at hsome
    cases hsome
  · exact ⟨w, s, hc, (atKeccak_of_eq hA).symm.trans hsome⟩

end
end LeanVM.Guest.Child
