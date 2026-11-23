/-
  LeanVM.Guest.EndExecHonest

  The executor's completeness on the guest for children the verifier accepts, unless a child's
  proof exhibits a Keccak-256 collision, and for children carrying honest proofs, and the composed
  prover's proof accepted, given `ExecGaps`.
-/

module

public import LeanVM.Guest.EndExec
public import LeanVM.Guest.HonestChildren
public import LeanVM.Guest.Child.Collision
public import LeanVM.Prover.End

@[expose] public section

/-!
# The executor on accepted and on honest children

`honestExecution_complete_of_childrenOk`, given `ExecGaps`: a node within the deployed limits whose
children the guest program accepts (`ChildrenOk`) is within the budget (`budget_of_limits`), so the
executor runs the guest to completion on its advice (`execute_guest_complete`).
`honestExecution_complete_on_accepted_children : AdviceComplete honestAdvice`: a node `NodeRelation`
admits under the deployed seed has acceptable children, or a child's proof exhibits a Keccak-256
collision (`Child.acceptableChildren_or_collide`). Its children carrying honest proofs are
acceptable too (`acceptableChildren_of_honest`): `honestExecution_ok_on_honest_children`.
`guest_prover_complete`: so the composed prover (the advice generator, the executor,
`leanVmHonestProver`) makes a proof that the verifier rejects, or fails to make, with probability
at most `2^-256` in the random-permutation model (`completeness_holds`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Completeness
open LeanVM.Prover.Exec
open scoped ENNReal

variable {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {X Pro : Ref → St → Prop}

/-- **The executor runs the guest program to completion on the guest's advice** on every node within
the deployed limits whose children the guest program accepts. -/
theorem honestExecution_complete_of_childrenOk (G : ExecGaps Ks Km E0 X Pro) (statement : NodeStatement)
    (witness : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness)
    (hlim : DeployedLimits statement witness)
    (hok : ChildrenOk (bytecodeWords guestProgram) (deployedSeed guestProgram) witness) :
    ∃ execution, guestRun honestAdvice statement witness = .ok execution ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      execution.committedSize ≤ 2 ^ 30 :=
  execute_guest_complete G _ _ _ hrel (GuestLimits.of_limits hlim) hok (budget_of_limits hlim hok)

/-- **The executor runs the guest program to completion on the guest's advice** on every node within
the deployed limits, unless a child's proof exhibits a Keccak-256 collision
(`AdviceComplete honestAdvice`). -/
theorem honestExecution_complete_on_accepted_children (G : ExecGaps Ks Km E0 X Pro) :
    AdviceComplete honestAdvice := fun statement witness hrel hlim ↦
  (Child.acceptableChildren_or_collide End.bytecode_length hrel).imp_left
    (honestExecution_complete_of_childrenOk G statement witness hrel hlim)

/-- **`honestExecution` on honest children**: `honestExecution_complete_of_childrenOk` with
`honestExecution`, honest children being acceptable. -/
theorem honestExecution_ok_on_honest_children (G : ExecGaps Ks Km E0 X Pro) (statement : NodeStatement)
    (witness : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness)
    (hlim : DeployedLimits statement witness) (hon : ∀ child ∈ witness.children, HonestChild child) :
    ∃ t, honestExecution (deployedSeed guestProgram) statement witness = .ok t ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ∧
      t.committedSize ≤ 2 ^ 30 :=
  let ⟨t, he, hv, hsz⟩ := honestExecution_complete_of_childrenOk G statement witness hrel hlim
    (acceptableChildren_of_honest hrel hon)
  ⟨t, honestExecution_of_execute he, hv, hsz⟩

open OracleComp OracleSpec in
/-- **The composed prover's proof is accepted**, in the random-permutation model: on every node
within the deployed limits whose children carry honest proofs, the executor's run on the guest's
advice is an execution whose proof by `leanVmHonestProver`, at an inverse rate `2^ρ`, `1 ≤ ρ ≤ 4`,
with `2^35` nonces per proof of work, the verifier rejects with probability at most `2^-256`. -/
theorem guest_prover_complete (G : ExecGaps Ks Km E0 X Pro) (statement : NodeStatement)
    (witness : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness)
    (hlim : DeployedLimits statement witness) (hon : ∀ child ∈ witness.children, HonestChild child) :
    ∃ t, guestRun honestAdvice statement witness = .ok t ∧ ∀ ρ, 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← completenessExperiment leanVmHonestProver guestProgram
          (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ρ (2 ^ 35)}[
          v = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  obtain ⟨t, he, hv, hsz⟩ := honestExecution_complete_of_childrenOk G statement witness hrel hlim
    (acceptableChildren_of_honest hrel hon)
  exact ⟨t, he, fun ρ hρ ↦ LeanVM.completeness_holds _ _ t ρ hv hsz hρ⟩

end LeanVM.Guest.EndExec

end
