/-
  Rv64mc.Spec.Transcript.Finish

  The contract of `Transcript::finish(self) -> Result<(), VerifierError>`: the transcript, passed by reference, in
  `a0`; the result's tag in `a0` (`Layouts.ResultUnit`: `Ok` is the niche value). It returns `Ok` exactly where the
  mirror's `Model.TM.finish` succeeds: the stream and the openings read to their ends. It writes nothing.
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.Finish

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x10) t

def Post (t : Model.TState) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag ↔ (Model.TM.finish.run t).isSome

/-- **The contract of `Transcript::finish`**, function `i` of `p` with `need` bytes of stack (it has no frame and
    calls nothing), for every transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post t)

end Rv64mc.Spec.Transcript.Finish
