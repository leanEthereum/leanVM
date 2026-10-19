/-
  LeanVM.Guest.EndFinalComplete

  The completeness end theorem for the deployed guest bytecode, within the deployed budget
  `B2C.b2cBudget'`, from checker K's three open B2 facts.
-/

module

public import LeanVM.Guest.EndCompleteFinal

namespace LeanVM.Guest.End

@[expose] public section

/-- **Completeness of the deployed guest, from checker K's open facts**: for `NodeRel` within the
limits and the caps, and the node within `B2C.b2cBudget'`, a valid execution of the guest on the
statement's digest. -/
theorem guest_complete_of_open (hrun : B2C.B2cRun) (hb2 : B2C.B2cB2) (hcount : B2C.B2cCount) :
    GuestCompleteWithin B2C.b2cBudget' :=
  B2C.guest_complete_b2c' hrun hb2 hcount

end

end LeanVM.Guest.End
