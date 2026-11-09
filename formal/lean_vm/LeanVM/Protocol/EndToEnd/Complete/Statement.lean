/-
  LeanVM.Protocol.EndToEnd.Complete.Statement

  Completeness in the two-oracle random-oracle model (`LeanVM/Protocol/Rom/Statement.lean`, a step
  of the proof of `Statement/LeanVm.lean`'s) proved: the honest prover, run as the adversary of the
  random-oracle experiment, makes the verifier reject with probability at
  most `completenessError fuel`.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Rom
public import LeanVM.Protocol.Rom.Statement
public import LeanVM.Protocol.WithHash

/-!
# Completeness in the random-oracle model, as `LeanVM/Protocol/Rom/Statement.lean` states it

The statement's experiment (`LeanVM.experiment`) runs the adversary, then the verifier, against
one lazily sampled pair of random oracles (Keccak-256 and Keccak-f[1600]), and records the
verdict, the final cache and the adversary's cache. Forgetting the adversary's cache it is the
random-oracle theorem's experiment (`experiment_map_romExperiment`), so `romComplete_leanVm`
bounds the probability that the verifier rejects the honest prover's proof
(`completeness_le`), by the statement's `completenessError`, which is `completenessError`
evaluated (`completenessError_eq`):

  `completenessError fuel = (12008 + 48019 · (2^27 + 2·fuel + 2)) · (1 - 2^-17)^fuel`,

below `2^-257` at a fuel of `2^25` nonces per proof of work (`statement_completenessError_le`).
`completeness_holds` is `LeanVM.CompletenessRom`, with the honest prover `honestProverRom`.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Rom LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-- The statement's verifier, on a statement and a proof. -/
abbrev stmtVerifier : LeanVM.ProgramAndInput × LeanVM.Protocol.Compile.Proof → OracleComp LeanVM.KeccakCalls Bool :=
  fun z ↦ LeanVM.verifierWithHash LeanVM.callKeccak256 LeanVM.callKeccakF1600 z.1.1 z.1.2 z.2

/-- **The statement's experiment, without the adversary's cache, is the random-oracle theorem's
experiment.** -/
theorem experiment_map_romExperiment (A : LeanVM.Adversary) :
    (fun z ↦ (z.1, z.2.1)) <$> LeanVM.experiment A = romExperiment A stmtVerifier := by
  rw [romExperiment_eq, LeanVM.experiment]
  simp only [map_bind, map_pure]
  refine bind_congr fun p ↦ ?_
  simp [map_eq_bind_pure_comp]

/-- **The honest prover of the statement**: the proof of `honestComp`, with its statement. -/
noncomputable def honestProverRom (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : LeanVM.Adversary :=
  (fun proof ↦ ((prog, input), proof)) <$> honestComp prog input t ρ fuel

/-- The statement's completeness error is `completenessError`, evaluated. -/
theorem completenessError_eq (fuel : ℕ) :
    LeanVM.completenessError fuel = completenessError fuel := by
  have hc : leanVmCost = 48019 := by decide
  have hQ : completenessQueries fuel = 12008 + 48019 * (2 ^ 27 + 2 * fuel + 2) := by
    rw [completenessQueries, proverFactor, costHeight, hc, leanVmQueryBound_eq]
    ring
  rw [LeanVM.completenessError, completenessError, hQ]
  rfl

/-- **Completeness in the statement's experiment.** For a valid execution whose committed size
is at most `2^28`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, and a fuel of at most `2^64`
nonces: the verifier rejects the honest prover's proof with probability at most
`completenessError fuel`. -/
theorem completeness_le {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← LeanVM.experiment (honestProverRom prog input t ρ fuel)}[z.rejected] ≤
      LeanVM.completenessError fuel := by
  have hV : (fun π ↦ LeanVM.verifierWithHash LeanVM.callKeccak256 LeanVM.callKeccakF1600 prog input π) =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  have h := romComplete_leanVm hv hbudget hρ hfuel
  rw [← hV, ← completenessError_eq] at h
  have e := prEvent_map (LeanVM.experiment (honestProverRom prog input t ρ fuel))
    (fun z ↦ (z.1, z.2.1)) (fun z ↦ z.1.2 = false)
  rw [experiment_map_romExperiment] at e
  refine (le_of_eq e.symm).trans ?_
  unfold honestProverRom
  rw [romExperiment_map, prEvent_map]
  exact h

/-- **The numbers**: at a fuel of `2^25` nonces per proof of work, the statement's completeness
error is below `2^-257`. -/
theorem statement_completenessError_le :
    LeanVM.completenessError (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 := by
  rw [completenessError_eq]
  exact completenessError_le

/-- **Completeness holds**, with the honest prover `honestComp` (which always makes a proof). -/
theorem completeness_holds : LeanVM.CompletenessRom :=
  ⟨fun prog input t ρ fuel ↦ some <$> honestComp prog input t ρ fuel,
    fun _ _ _ _ _ hv hbudget hρ hfuel ↦ by
      simp only [Functor.map_map, Option.getD_some]
      exact completeness_le hv hbudget hρ hfuel⟩

end
end LeanVM.Protocol.EndToEnd.Complete
