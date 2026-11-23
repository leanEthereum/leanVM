/-
  LeanVM.Guest.EndExecHonest

  The executor's completeness on the guest for children the verifier accepts, unless a child's
  proof exhibits a Keccak-256 collision, given `ExecGaps`.
-/

module

public import LeanVM.Guest.EndExec
public import LeanVM.Guest.HonestChildren
public import LeanVM.Guest.Child.Collision

@[expose] public section

/-!
# The executor on accepted children

`honestExecution_complete_of_childrenOk`, given `ExecGaps`: a node within the deployed limits whose
children the guest program accepts (`ChildrenOk`) is within the budget (`budget_of_limits`), so the
executor runs the guest to completion on its advice (`execute_guest_complete`).
`honestExecution_complete_on_accepted_children : AdviceComplete honestAdvice`: a node `NodeRelation`
admits under the deployed seed has acceptable children, or a child's proof exhibits a Keccak-256
collision (`Child.acceptableChildren_or_collide`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Completeness
open LeanVM.Prover.Exec

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

end LeanVM.Guest.EndExec

end
