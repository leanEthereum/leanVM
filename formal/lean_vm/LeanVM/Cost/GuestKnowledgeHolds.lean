module

public import LeanVM.Cost.GuestKnowledgeVs
public import LeanVM.Guest.B1.VerifySub.PhOodRingOod
public import LeanVM.Guest.B1.VerifySub.PhOodRingRing
public import LeanVM.Guest.B1.VerifySub.PhOpen
public import LeanVM.Guest.B1.VerifySub.PhLink

/-!
# The guest's knowledge soundness

`guestKnowledgeSoundness_holds`: `GuestKnowledgeSoundness compiledGuestWitnessDecoder`, from
`verify_sub`'s phases, all proved: `phOod`, `phLink`, `phRing`, and the opening from the
out-of-domain phase (`phOpen_of_ood`).
-/

namespace LeanVM.Cost

open LeanVM.Node LeanVM.Guest.B1.VerifySub

public section

/-- **Knowledge soundness of the guest, for the compiled decoder.** -/
theorem guestKnowledgeSoundness_holds : GuestKnowledgeSoundness compiledGuestWitnessDecoder :=
  guestKnowledgeSoundness_of_phases phOod phLink phRing (phOpen_of_ood phOod)

end

end LeanVM.Cost
