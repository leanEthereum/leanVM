/-
  LeanVM.Guest.Backend.Guest.B2.Downstream

  The end theorems that consume `B2SoundL`, from the back end's proof of it instead of the
  certificates' (`EndSound.lean`'s `b2SoundL_of`).
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Guest.Backend.Guest.B2.Bridge

/-!
# The consumers of B2, from the back end

`EndSound.lean` feeds `guest_knowledge_V` and `decode_binds_V` (`EndKnow.lean`) the value
`b2SoundL_of vsDimsKnown_proved vsKnown_proved hwalk : B2SoundL`, built on the certificate checks.
Here the same theorems take `b2SoundL_backend h hagree`, so the statement `Bridge.lean` proves is the
one the assembly consumes. Neither theorem needs the walks' cut obligations (`WalkKnown`): the back
end's obligations (`guest_obligations`) cover them.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.End LeanVM.Guest.B1

@[expose] public section

variable {fns : List Lowered} {slots : Array KVal}
  {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof}

/-- **Soundness of the deployed guest, its witness named**, from the back end's B2 and
`verify_sub`'s statement. -/
theorem guest_knowledge_backend (h : GuestCompiles fns slots) (hagree : LocsAgree)
    (hv : B1.Main.SubSoundW bytecode piOf) :
    MemoryGuestKnowledge guestProgram (End.decodeV piOf) :=
  End.guest_knowledge_V (b2SoundL_backend h hagree) hv

/-- **What a consumer learns**, from the back end's B2 and `verify_sub`'s statement. -/
theorem decode_binds_backend (h : GuestCompiles fns slots) (hagree : LocsAgree)
    (hv : B1.Main.SubSoundW bytecode piOf)
    {input : PublicInput} {t : Execution guestProgram} (hvt : ValidExecution guestProgram input t)
    {iv : Digest} {s₀ : NodeStatement} (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode)
    (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((End.decodeV piOf t.memory).seed = iv ∧ (End.decodeV piOf t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (End.decodeV piOf t.memory).seed
        (End.decodeV piOf t.memory).statement iv s₀) :=
  End.decode_binds_V (b2SoundL_backend h hagree) hv hvt hs₀ hpub

end
end LeanVM.Guest.Backend.B2
