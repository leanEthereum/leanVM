/-
  LeanVM.Guest.EndFinalComplete

  The completeness end theorem for the deployed guest bytecode, within the deployed budget
  `B2C.b2cBudget'`: checker K's B2 facts (`kfacts_run`, `b2cB2`, `b2cCount`) plugged into
  `guest_complete_of_open`.
-/

module

public import LeanVM.Guest.EndCompleteFinal
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.KFacts

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd
open scoped ENNReal

@[expose] public section

/-- **Completeness of the deployed guest, from checker K's open facts**: for `NodeRel` within the
limits and the caps, and the node within `B2C.b2cBudget'`, a valid execution of the guest on the
statement's digest. -/
theorem guest_complete_of_open (hrun : B2C.B2cRun) (hb2 : B2C.B2cB2) (hcount : B2C.B2cCount) :
    GuestCompleteWithin B2C.b2cBudget' :=
  B2C.guest_complete_b2c' hrun hb2 hcount

/-- **Completeness of the deployed guest** (GOAL.txt, checkpoint 5): for `NodeRel` within the
limits and the caps, and the node within `B2C.b2cBudget'`, a valid execution of the guest on the
statement's digest within the verifier's committed size. -/
theorem guest_complete : GuestCompleteWithin B2C.b2cBudget' :=
  guest_complete_of_open (fun hdr T _ ↦ B2C.kfacts_run hdr T) B2C.b2cB2 B2C.b2cCount

/-- **The aggregate's completeness against the random oracle**, from `guest_complete`: the honest
prover's proof of that execution is rejected with probability at most `completenessError fuel`. -/
theorem aggregate_complete {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRel bytecode seed s w) (hlim : Limits s w) (hcap : CapsAgree seed w)
    (hbudget : B2C.b2cBudget'.size (work s w) ≤ 2 ^ 28) :
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      ∀ ρ fuel, 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
        Pr{let z ← experiment (honestProver guest (publicInputOf (statementDigest seed s)) t ρ fuel)}[
          z.1.2 = false] ≤ completenessError fuel := by
  obtain ⟨t, hv, hsize⟩ := guest_complete seed s w hrel hlim hcap hbudget
  exact ⟨t, hv, fun _ _ hρ hfuel ↦ completeness hv hsize hρ hfuel⟩

end

end LeanVM.Guest.End
