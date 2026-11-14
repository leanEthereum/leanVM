/-
  LeanVM.Guest.EndExecHonest

  The executor's completeness on the guest for children carrying honest proofs, and the composed
  prover's proof accepted, given `ExecGaps`.
-/

import LeanVM.Guest.EndExec
import LeanVM.Guest.HonestChildren
import LeanVM.Prover.End

/-!
# The executor on honest children

`guestExecution_complete_on_honest_children : GuestExecutionComplete guestAdvice`, given
`ExecGaps`: a node within the deployed limits, under the deployed seed, whose children carry honest
proofs, has acceptable children (`acceptableChildren_of_honest`) and is within the budget
(`budget_of_limits`), so the executor runs the guest to completion on its advice
(`execute_guest_complete`). `guest_prover_complete`: so the composed prover (the advice generator,
the executor, `leanVmHonestProver`) makes a proof that the verifier rejects with probability at most
`2^-256`, and that the verifier refusing every zero challenge rejects, or that it fails to make, with
probability at most `2^-100`, in the random-permutation model (`completeness_holds`,
`honest_proof_rarely_refused`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Completeness
open LeanVM.Prover.Exec
open scoped ENNReal

variable {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {X Pro : Ref → St → Prop}

/-- **The executor runs the guest program to completion on the guest's advice** on every node within
the deployed limits whose children carry honest proofs (`GuestExecutionComplete guestAdvice`). -/
theorem guestExecution_complete_on_honest_children (G : ExecGaps Ks Km E0 X Pro) :
    GuestExecutionComplete guestAdvice := by
  intro statement witness hrel hlim hon
  have hok := acceptableChildren_of_honest hrel hon
  exact execute_guest_complete G _ _ _ hrel (GuestLimits.of_limits hlim) hok (budget_of_limits hlim hok)

/-- **`guestExecution` on honest children**: `guestExecution_complete_on_honest_children` with
`guestExecution`. -/
theorem guestExecution_ok_on_honest_children (G : ExecGaps Ks Km E0 X Pro) (statement : NodeStatement)
    (witness : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness)
    (hlim : DeployedLimits statement witness) (hon : ∀ child ∈ witness.children, HonestChild child) :
    ∃ t, guestExecution (deployedSeed guestProgram) statement witness = .ok t ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ∧
      t.committedSize ≤ 2 ^ 30 :=
  let ⟨t, he, hv, hsz⟩ := guestExecution_complete_on_honest_children G statement witness hrel hlim hon
  ⟨t, guestExecution_of_execute he, hv, hsz⟩

open OracleComp OracleSpec in
/-- **The composed prover's proof is accepted**, in the random-permutation model: on every node within
the deployed limits whose children carry honest proofs, the executor's run on the guest's advice is
an execution whose proof by `leanVmHonestProver`, at an inverse rate `2^ρ`, `1 ≤ ρ ≤ 4`, with `2^35`
nonces per proof of work, the verifier rejects with probability at most `2^-256`, and which the
honest prover fails to prove, or whose proof the verifier refusing every zero challenge rejects,
with probability at most `2^-100`. -/
theorem guest_prover_complete (G : ExecGaps Ks Km E0 X Pro) (statement : NodeStatement)
    (witness : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness)
    (hlim : DeployedLimits statement witness) (hon : ∀ child ∈ witness.children, HonestChild child) :
    ∃ t, guestRun guestAdvice statement witness = .ok t ∧ ∀ ρ, 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← completenessExperiment leanVmHonestProver guestProgram
          (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ρ (2 ^ 35)}[
          v = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 ∧
      Pr{let accepted ← Common.runWithRandomPermutation (do
          match ← LeanVM.leanVmHonestProver Common.queryPermutation guestProgram
              (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ρ
              (2 ^ 35) with
          | none => pure false
          | some proof =>
            verifierRefusingZero Common.queryPermutation guestProgram
              (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) proof)}[
          accepted = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 100 := by
  obtain ⟨t, he, hv, hsz⟩ := guestExecution_complete_on_honest_children G statement witness hrel hlim hon
  exact ⟨t, he, fun ρ hρ ↦ ⟨LeanVM.completeness_holds _ _ t ρ hv hsz hρ,
    honest_proof_rarely_refused _ _ t ρ hv hsz hρ⟩⟩

end LeanVM.Guest.EndExec
