module

public import LeanVM.Cost.Bounds.Guest.Budget
public import LeanVM.Guest.EndFinal
public import LeanVM.Guest.WalkKnownAll

/-!
# The guest's knowledge soundness, for the compiled decoder

**`guestKnowledgeSoundness_of (hb2 : B2SoundL) (hsub : SubSoundW bytecode vsPiOf) :
GuestKnowledgeSoundness compiledGuestWitnessDecoder`**: the compiled decoder program
(`Cost/DecoderSpec.lean`) computes the replaying decoder `End.decode` within its size bound and,
given B2 and `verify_sub`'s statement, within its budget (`decoderPriceWithinBudget`,
`Bounds/Guest/Budget.lean`: the budget's bound on the children's cursors reads the decoded
witness's soundness); `End.guestKnowledgeSoundness_of_spec` composes it with the decoder's
soundness (`End.guest_knowledge_of`). `guestKnowledgeSoundness_of_obligations`: the same from B2's
obligations (`End.b2SoundL_of`); `guestKnowledgeSoundness_of_vs`: from `verify_sub`'s two (`VsKapsKnown`,
`VsGmvKnown`), the walks' proved (`walkKnown_proved`).
-/

namespace LeanVM.Cost

open LeanVM.Guest LeanVM.Guest.End LeanVM.Node

public section

/-- **Knowledge soundness of the guest, for the compiled decoder**, from B2 and `verify_sub`'s
statement with its proof named by `vsPiOf`. -/
theorem guestKnowledgeSoundness_of (hb2 : B2SoundL)
    (hsub : B1.Main.SubSoundW bytecode B1.VerifySub.vsPiOf) :
    GuestKnowledgeSoundness compiledGuestWitnessDecoder :=
  guestKnowledgeSoundness_of_spec
    (decoderProgram_spec (Bounds.Guest.decoderPriceWithinBudget hb2 hsub)) hb2 hsub

/-- **Knowledge soundness of the guest, for the compiled decoder**, from B2's obligations and
`verify_sub`'s statement with its proof named. -/
theorem guestKnowledgeSoundness_of_obligations (hkaps : VsKapsKnown) (hgmv : VsGmvKnown)
    (hwalk : WalkKnown) (hsub : B1.Main.SubSoundW bytecode B1.VerifySub.vsPiOf) :
    GuestKnowledgeSoundness compiledGuestWitnessDecoder :=
  guestKnowledgeSoundness_of (b2SoundL_of hkaps hgmv hwalk) hsub

/-- **Knowledge soundness of the guest, for the compiled decoder**, from `verify_sub`'s B2
obligations and its statement with its proof named, the walks' obligations proved. -/
theorem guestKnowledgeSoundness_of_vs (hkaps : VsKapsKnown) (hgmv : VsGmvKnown)
    (hsub : B1.Main.SubSoundW bytecode B1.VerifySub.vsPiOf) :
    GuestKnowledgeSoundness compiledGuestWitnessDecoder :=
  guestKnowledgeSoundness_of_obligations hkaps hgmv walkKnown_proved hsub

end

end LeanVM.Cost
