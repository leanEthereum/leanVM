/-
  LeanVM.Protocol.LeanVM

  The proof of the two statements of `LeanVM/Spec/Statement.lean`: knowledge soundness of the
  leanVM verifier in the random-oracle model, at 128 bits per query, and completeness.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Statements
public import LeanVM.Protocol.EndToEnd.Complete.Rom

/-!
# leanVM, end to end

The statements are in `LeanVM/Spec/` (the ISA, the verifier, and `Statement.lean`), which
imports nothing else from the repository. This page proves them, `knowledgeSoundness_holds` and
`completeness_holds`, with an explicit extractor and honest prover, and gives the numbers.

**Knowledge soundness** (`knowledgeSoundness`): an adversary making at most `Q` queries to the
random oracle outputs a statement (a program and a public input) and a proof, choosing all three
after querying the oracle. The probability that the verifier accepts while the program's last
instruction is not a `JUMP` and the extracted execution (`extract`: the memory image the proof
commits to, run until it halts) is not a valid execution of the program on the public input is at
most `soundnessError Q = (Q + 13213) · (2^-128 + 5·(Q + 13213)/2^256)`, which is at most `2^-63`
for `Q ≤ 2^64` (`soundnessError_le`). The `2^-128` is per oracle query: every group of the
protocol's challenges, discounted by the proof of work before it, escapes with probability at
most `2^-128`, certified for every admissible size and rate (`Whir.Params.Deployed`).

**Completeness** (`completeness`): for a valid execution whose committed size
(`Trace.committedSize`: the memory, the bytecode and a table per opcode, each at its height) is at
most `2^28`, the most the verifier admits, the honest prover
(`honestProver`), run in the same random-oracle experiment, makes the verifier reject with probability at most
`completenessError fuel`, which is below `2^-128` at a fuel of `2^25` nonces per proof of work
(`completenessError_le`). The honest prover is a specification, not an implementation.

**Scope and trust.**

* BLAKE2s is modelled as a random oracle.
* The extractor is information-theoretic, not efficient: a classical choice in the list of
  codewords near the committed word.
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths (shared siblings per batch, `MerkleOpenings::Pruned`), which
  the deployed `leanvm_core::cpu::verify` expands into these paths and checks more strictly; that
  expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Blake2sHash
open Air.Flat (EnsembleWitness)
open scoped ENNReal

@[expose] public section

/-- `verify` is the transcription of the deployed verifier, run with BLAKE2s
(`LeanVM.Protocol.Verifier.verify`, what `lake exe leanvm-verify` runs). -/
theorem verify_eq (prog : Program) (input : PublicInput) (proof : Proof) :
    verify prog input proof =
      LeanVM.Protocol.Verifier.verify (Front.bytecodeWords prog) (Complete.publicDigest input)
        proof :=
  rfl

/-- The experiment is the generic adversary-then-verifier experiment the proofs are about. -/
theorem experiment_eq (A : Adversary) :
    experiment A = Rom.romExperiment A fun z ↦ verifier queryH z.1.1 z.1.2 z.2 :=
  rfl

/-! ## Knowledge soundness -/

/-- The execution of `prog` on a memory image: the image, run from `(1, 1)` for the least number
of steps after which it halts at `(g^(N − 1), 1)`; `none` if it never does. -/
noncomputable def haltingRun (prog : Program) {κ : ℕ} (image : MemImage κ) : Option (Trace prog) :=
  open Classical in
  if h : ∃ n, run prog image n Regs.initial = some (Regs.final prog) then
    some ⟨κ, image, Nat.find h⟩
  else none

/-- **The extractor**: from the oracle's answers and the proof, the execution the proof commits
to: the memory image of the committed stack (the stack's commitment is read off the answers to
the Merkle queries, and the stack is the codeword of its Johnson list satisfying the constraints,
chosen classically), run until it halts. -/
noncomputable def extract (prog : Program) (input : PublicInput) (answers : HashSpec.QueryCache)
    (proof : Proof) : Option (Trace prog) :=
  (Sound.extractStack prog input answers proof).bind fun x ↦
    let image := imageOf (witnessOf Blake2sFlock.blake2sFlockSpec prog x.1 x.2).data
    haltingRun prog image.2

/-- A witness representing a valid execution has its image's halting run, valid. -/
theorem haltingRun_valid {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Trace prog}
    (hrep : AssignmentRepresents w t) (hv : ValidExecution prog input t) :
    ∃ t', haltingRun prog (imageOf w.data).2 = some t' ∧ ValidExecution prog input t' := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  generalize imageOf w.data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  have h : ∃ n, run prog image' n Regs.initial = some (Regs.final prog) := ⟨steps, hv.2⟩
  exact ⟨⟨_, image', Nat.find h⟩, by simp only [haltingRun, h, ↓reduceDIte], hv.1,
    Nat.find_spec h⟩

/-- **Knowledge soundness in the random-oracle model.** For an adversary making at most `Q`
queries, which chooses the program, the public input and the proof, the verifier accepts while
the program's last instruction is not a `JUMP` and the extracted execution is not a valid
execution of the program on the public input with probability at most `soundnessError Q`. -/
theorem knowledgeSoundness {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[Breaks extract z] ≤ soundnessError Q := by
  have hV : (fun z : Statement × Proof ↦ verifier queryH z.1.1 z.1.2 z.2) =
      Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram := by
    funext z
    rw [Sound.verifierFam_leanVm, verifierComp_leanVm]
    rfl
  have h := Sound.romSound_of_imp Sound.anyProgram Sound.anyCert Sound.leanVmSeeds
    (fun x ↦ Sound.rootOk_stmtHistory x) Sound.εLean Sound.anyCert_bound A Q hA
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam
    (fun z c ↦ SentinelSafe z.1.1 ∧
      ¬ ∃ t, extract z.1.1 z.1.2 c z.2 = some t ∧ ValidExecution z.1.1 z.1.2 t)
    (fun z c hv hb ↦ by
      simp only [Sound.leanVmSeeds, Sound.nodeAt_stmtHistory] at hv
      refine Sound.doomed_of_doomedRun hv (Sound.doomed_of_not_extracted z.1.1 z.1.2 hv
        fun ⟨s, q, hx, hs, hM⟩ ↦ hb.2 ?_)
      obtain ⟨t, hrep, ht⟩ := execution_of_extracted Blake2sFlock.blake2sFlockSpec hb.1 hs hM
      obtain ⟨t', ht', hv'⟩ := haltingRun_valid hrep ht
      exact ⟨t', by simp only [extract, hx, Option.bind_some]; exact ht', hv'⟩)
  rw [leanVmQueryBound_eq] at h
  rw [experiment_eq, hV]
  refine (le_of_eq ?_).trans (h.trans (le_of_eq ?_))
  · rfl
  · rw [soundnessError, failBound]
    rfl

/-- **The numbers**: against `2^64` queries, the soundness error is at most `2^-63`. -/
theorem soundnessError_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  have h := Sound.leanVm_bound_le hQ
  rw [failBound] at h
  exact (le_of_eq (by rfl)).trans h

/-! ## Completeness -/

/-- **The honest prover**: the proof of the execution `t` at the commitment's inverse rate `2^ρ`,
every hash a query to the random oracle, each proof-of-work search trying at most `fuel` nonces
(the empty proof if one fails). A specification: it takes a witness of leanISA's constraint
system representing the execution (a classical choice), pads its tables with the public padding
rows, and runs the honest strategy of every phase through the Fiat-Shamir transform. -/
noncomputable def honestProver (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) : Adversary :=
  (fun proof ↦ ((prog, input), proof)) <$> Complete.honestComp prog input t ρ fuel

theorem completenessError_eq (fuel : ℕ) :
    completenessError fuel = Complete.completenessError fuel := by
  have hc : leanVmCost = 13210 := by decide
  have hQ : Complete.completenessQueries fuel = 13216 + 13210 * (2 ^ 27 + fuel + 1) := by
    rw [Complete.completenessQueries, proverFactor, costHeight, hc, leanVmQueryBound_eq]
    ring
  rw [completenessError, Complete.completenessError, hQ]
  rfl

/-- **Completeness.** For a valid execution whose committed size is at most `2^28`, at an inverse
rate `2^ρ` with `1 ≤ ρ ≤ 4`: the verifier rejects the honest prover's proof, in the random-oracle
experiment, with probability at most `completenessError fuel`. -/
theorem completeness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel := by
  have hV : (fun π ↦ verifier queryH prog input π) =
      verifierComp (leanVmSeed (Front.bytecodeWords prog) (Complete.publicDigest input))
        (leanVmProgram (Front.bytecodeWords prog) (Complete.publicDigest input)) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  have h := Complete.romComplete_leanVm hv hbudget hρ hfuel
  rw [← hV, ← completenessError_eq] at h
  rw [experiment_eq]
  unfold honestProver
  rw [Rom.romExperiment_map, prEvent_map]
  exact h

/-- **The numbers**: at a fuel of `2^25` nonces per proof of work, the completeness error is
below `2^-128`. -/
theorem completenessError_le : completenessError (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [completenessError_eq]
  exact Complete.completenessError_le

/-! ## The statements of `LeanVM/Spec/Statement.lean` -/

/-- **Knowledge soundness holds**, with the extractor `extract`. -/
theorem knowledgeSoundness_holds : KnowledgeSoundness :=
  ⟨extract, fun _ _ hA ↦ knowledgeSoundness hA⟩

/-- **Completeness holds**, with the honest prover `honestProver`. -/
theorem completeness_holds : Completeness :=
  ⟨Complete.honestComp, fun _ _ _ _ _ hv hbudget hρ hfuel ↦ completeness hv hbudget hρ hfuel⟩

end
end LeanVM
