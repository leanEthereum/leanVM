/-
  LeanVM.Prover.End

  The completeness end theorems, for the statement's honest prover `LeanVM.leanVmHonestProver`
  (`LeanVM.Prover.prove`, `Statement/Prover/Prove.lean`).
-/

import LeanVM.Prover.Assemble
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash
import LeanVM.Guest.ExperimentBridge
import LeanVM.Guest.AcceptableChild

/-!
# The completeness end theorems

`LeanVM.leanVmHonestProver`, the statement's executable honest prover with the oracle calls, is the
specification's honest prover at the execution's witness (`LeanVM.Prover.prove_eq_honestComp`,
`specOnValid_prove`, `childSpec_prove`, `LeanVM/Prover/Assemble.lean`), so the completeness
theorems for such a prover (`completeness_of_spec`, `guestChildComplete_of_spec`,
`LeanVM/Prover/Complete.lean`) prove the end statements:

* `LeanVM.completeness_holds : Completeness`;
* `LeanVM.Guest.Budget.guest_child_complete : GuestChildComplete`.
-/

namespace LeanVM

open LeanVM.Prover

/-- Completeness in the experiment with the two calls, for the honest prover with them. -/
theorem completenessWithHash_holds : CompletenessWithHash :=
  completeness_of_spec LeanVM.proverWithHash specOnValid_prove_honest

/-- **Completeness holds** (in the random-permutation model), for the honest prover
`LeanVM.leanVmHonestProver`: its experiment is the one with the two calls
(`completeness_of_withHash`). -/
theorem completeness_holds : Completeness :=
  completeness_of_withHash completenessWithHash_holds

/-- Both parts of `GuestChildCompleteWithHash`, for the honest prover with the two calls. -/
theorem Guest.Budget.guestChildCompleteWithHash_holds : Guest.Budget.GuestChildCompleteWithHash :=
  guestChildComplete_of_spec LeanVM.proverWithHash specOnValid_prove childSpec_prove

/-- **The honest prover's proofs of guest executions are children the guest accepts**: both parts
of `GuestChildComplete` for `LeanVM.leanVmHonestProver`. -/
theorem Guest.Budget.guest_child_complete : Guest.Completeness.GuestChildComplete :=
  Guest.Budget.guestChildComplete_of_withHash Guest.Budget.guestChildCompleteWithHash_holds

end LeanVM
