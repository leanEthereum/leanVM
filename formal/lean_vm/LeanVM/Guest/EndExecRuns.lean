module

public import LeanVM.Guest.EndExec
public import LeanVM.Guest.Budget.Runs

/-!
# The guest's execution on a reference run's node

`guestExecution_eq`: under the deployed seed, `guestExecution` is the executor on the reference's
public input and advice (`Complete/Open.lean` reads it).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Mode LeanVM.Guest.Completeness LeanVM.Guest.Budget
open LeanVM.Prover.Exec

@[expose] public section

/-- **The guest's execution on a reference run's node** is the executor on the reference's input and
advice, under the deployed seed. -/
theorem guestExecution_eq {r : Ref} (hseed : r.seed = deployedSeed guestProgram) :
    guestExecution guestProgram r.s r.w = execute guestProgram r.input r.adv := by
  simp only [guestExecution, Ref.input, Ref.adv, hseed]

end

end LeanVM.Guest.EndExec
