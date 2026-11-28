module

public import LeanVM.Cost.GuestKnowledge
public import LeanVM.Guest.VsKaps
public import LeanVM.Guest.B1.VerifySub.Sound

/-!
# The guest's knowledge soundness, given `verify_sub`'s open phases

`guestKnowledgeSoundness_of_phases`: `GuestKnowledgeSoundness compiledGuestWitnessDecoder` from
the phases of `verify_sub` still open (`PhOod`, `PhLink`, `PhRing`, `PhOpen`,
`B1/VerifySub/Phases.lean`): B2's obligations on `verify_sub` are proved (`vsKapsKnown_proved`,
`vsGmvKnown_proved`), and `verify_sub`'s statement follows from its phases (`subSoundW_of`).
-/

namespace LeanVM.Cost

open LeanVM.Guest LeanVM.Guest.End LeanVM.Node LeanVM.Guest.B1.VerifySub

public section

/-- **Knowledge soundness of the guest, for the compiled decoder**, given `verify_sub`'s open
phases. -/
theorem guestKnowledgeSoundness_of_phases (hOod : PhOod) (hLink : PhLink) (hRing : PhRing)
    (hOpen : PhOpen) : GuestKnowledgeSoundness compiledGuestWitnessDecoder :=
  guestKnowledgeSoundness_of_vs vsKapsKnown_proved vsGmvKnown_proved
    (subSoundW_of hOod hLink hRing hOpen _)

end

end LeanVM.Cost
