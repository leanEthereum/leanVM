/-
  LeanVM.Guest.Child.NZRom

  The child prover's proof against the statement's refusing verifier in the random-oracle model:
  rejected with probability at most `childCompletenessError fuel`, the ideal failure of the
  refusing verifier plus the proofs of work's misses plus a capacity collision.
-/

module

public import LeanVM.Protocol.Compile.Rom.Sharp
public import LeanVM.Guest.Child.Refusing
public import LeanVM.Protocol.EndToEnd.Complete.Rom
public import LeanVM.Protocol.EndToEnd.Complete.Theorem
public import LeanVM.Protocol.Verifier.Cost

/-!
# The refusing verifier, against the random oracles

`romChild_at`: `Rom.romCompleteSharp` at leanVM's program and seed, the refusing program
(`Limits.refusingZeroProgram`, the statement's `verifierRefusingZero`) refining the verifier
program, the honest strategy winning every interactive run; the ideal failure probability of the
refusing program is at most `(leanVmCost / 4) · |E|⁻¹`
(`failFrom_refusingZeroProgram_le`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Rom LeanVM.Protocol.KeccakHash OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-- `|E|⁻¹ = 2^-128`. -/
theorem epsE_eq : epsE = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  unfold epsE
  have h : Fintype.card E = 2 ^ 128 := by
    convert card_E using 1
    exact congrArg (@Fintype.card E) (Subsingleton.elim _ _)
  rw [h, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-- **The completeness error of the statement's refusing verifier** against the random oracles:
its ideal failure (`|E|⁻¹` per sample), a proof of work's
miss per quarter of the cost, and a capacity collision among the queries. -/
noncomputable def childCompletenessError (fuel : ℕ) : ℝ≥0∞ :=
  ((leanVmCost / 4 : ℕ) : ℝ≥0∞) * epsE + (leanVmCost : ℝ≥0∞) * missProb 27 ^ fuel +
    (EndToEnd.Complete.completenessQueries fuel : ℝ≥0∞) *
      ((EndToEnd.Complete.completenessQueries fuel : ℝ≥0∞) * 2⁻¹ ^ 256)

/-- **The specification's honest prover at a witness, against the statement's refusing
verifier, in the random-oracle model.** -/
theorem romChild_at {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)} {s : Sizes}
    (hw : HonestFor prog input t ρ w s) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest
        input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmProver prog s ρ (stackOf prog s w)) fuel)
        (verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
          (Limits.refusingZeroProgram (bytecodeWords prog) (publicInputDigest input)))}[
        z.1.2 = false] ≤
      childCompletenessError fuel := by
  obtain ⟨hρ, hw', hs', hadm', -⟩ := hw
  have hq := m3Honest_stackOf hw' hs'
  have hrun := runI_leanVmProgram hadm' hρ hq
  -- Unifying through the strategy unfolds it under Lean 4.35: name it first.
  generalize leanVmProver prog s ρ (stackOf prog s w) = S at hrun ⊢
  have hP := costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)
  have hR := Limits.refusingZeroProgram_refines (bytecodeWords prog) (publicInputDigest input)
  have h := Rom.romCompleteSharp (leanVmVerifierProgram (bytecodeWords prog)
    (publicInputDigest input)) _ hR S (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    (bits := 27) (by norm_num) hfuel (fun _ _ _ hg _ ↦ ((moves_leanVm_twentySeven prog _).after hg).1)
    hP (costs_of_refines hR hP)
  have hacc : S.AcceptsFrom (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      [] :=
    Strategy.acceptsFrom_of_runFrom _ [] (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2)
  have hf := failFrom_refusingZeroProgram_le hacc
    (LeanVM.Protocol.EndToEnd.Sound.grindThenSample_leanVmProgram _ _) hP
  have hQ : ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).hs.length + 1 +
      leanVmCost * proverFactor costHeight fuel +
      ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).hs.length + 1 +
        leanVmCost / 4) : ℕ) = EndToEnd.Complete.completenessQueries fuel := by
    simp only [leanVmSeed, List.length_cons, List.length_nil,
      EndToEnd.Complete.completenessQueries, leanVmQueryBound]
  rw [hQ] at h
  refine h.trans ?_
  unfold childCompletenessError
  exact add_le_add (add_le_add hf le_rfl) le_rfl

end
end LeanVM.Guest.Child
