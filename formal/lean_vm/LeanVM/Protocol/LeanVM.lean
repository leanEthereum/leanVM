/-
  LeanVM.Protocol.LeanVM

  Knowledge soundness (`LeanVM.Protocol.LeanVMSound`) and completeness of the leanVM verifier in
  the two-oracle random-oracle model (`LeanVM/Protocol/Rom/Statement.lean`): the step of the proofs
  of `Statement/LeanVm.lean`'s statements before the random-permutation model.
-/

module

public import LeanVM.Protocol.LeanVMSound
public import LeanVM.Protocol.EndToEnd.Complete.Statement

/-!
# leanVM, end to end

The statements are in `LeanVM/Spec/` (the ISA, the verifier, the extractor, `Statement.lean` and
`Rpm.lean`), which imports nothing else from the repository; their proofs
(`LeanVM/Protocol/LeanVMRpm.lean`) go through the two-oracle random-oracle model of
`LeanVM/Protocol/Rom/Statement.lean`. There, knowledge soundness, `knowledgeSoundnessRom_holds`,
is proved in `LeanVM.Protocol.LeanVMSound`, and its numbers in `LeanVM.Protocol.ErrorBounds`;
this page proves completeness, `completenessRom_holds`, with an explicit honest prover.

**Completeness** (`completenessRom`): for a valid execution whose committed size
(`Execution.committedSize`: the memory, the bytecode and a table per opcode, each at its height) is at
most `2^30`, the most the verifier admits, the honest prover
(`honestProver`), run in the same random-oracle experiment, makes the verifier reject with probability at most
`completenessError fuel`, which is below `2^-257` at a fuel of `2^33` nonces per proof of work
(`completenessError_le`). The honest prover is a specification, not an implementation.

**Scope and trust.**

* Keccak-256 and Keccak-f[1600] are independent random oracles here, the step of the proof before
  the random-permutation model of the statements.
* A proof is the Rust verifier's `Proof`: the scalar stream and one full Merkle path per query,
  with its position, grouped in phases (`Statement/LeanVmVerifier.lean`). Its wire encoding, which
  prunes the paths, is the statement's `Proof.fromBytes` / `Proof.toBytes`, proved to invert each
  other in `LeanVM/Wire/`.
* That `verifier` is the Rust verifier is test evidence: it accepts the Rust prover's proofs,
  and on mutated proofs it gives the Rust verifier's verdict every time
  (`scripts/fuzz-verifier.py`).
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open scoped ENNReal

@[expose] public section

/-! ## Completeness -/

/-- **The honest prover**: the proof of the execution `t` at the commitment's inverse rate `2^ρ`,
every hash a query to the random oracle for Keccak-256 and every permutation one to the random
oracle for Keccak-f[1600], each proof-of-work search trying at most `fuel` nonces (the empty proof
if one fails). A specification: it takes a witness of leanISA's constraint system representing the
execution (a classical choice), pads its tables with the public padding rows, and runs the honest
strategy of every phase through the Fiat-Shamir transform (`Complete.honestProverRom`). -/
noncomputable def honestProver (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : Adversary :=
  Complete.honestProverRom prog input t ρ fuel

/-- The statement's completeness error is the random-oracle theorem's,
`(13263 + 53036 · (2^27 + 2·fuel + 2)) · (1 - 2^-25)^fuel`. -/
theorem completenessError_eq (fuel : ℕ) :
    completenessError fuel = Complete.completenessError fuel :=
  Complete.completenessError_eq fuel

/-- **Completeness in the two-oracle random-oracle model.** For a valid execution whose committed size is at most `2^30`, at an inverse
rate `2^ρ` with `1 ≤ ρ ≤ 4`: the verifier rejects the honest prover's proof, in the random-oracle
experiment, with probability at most `completenessError fuel`. -/
theorem completenessRom {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 30) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel :=
  Complete.completeness_le hv hbudget hρ hfuel

/-- **The numbers**: at a fuel of `2^33` nonces per proof of work, the completeness error is
below `2^-257`. -/
theorem completenessError_le : completenessError (2 ^ 33) ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 :=
  Complete.statement_completenessError_le

/-! ## The statement of `LeanVM/Protocol/Rom/Statement.lean` -/

/-- **Completeness in the two-oracle random-oracle model holds**, with the honest prover
`honestProver`. -/
theorem completenessRom_holds : CompletenessRom :=
  Complete.completeness_holds

end
end LeanVM
