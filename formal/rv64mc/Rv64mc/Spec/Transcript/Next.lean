/-
  Rv64mc.Spec.Transcript.Next

  The contract of `Transcript::next(&mut self) -> Result<E, VerifierError>`: the result's slot (`sret`) in `a0`, the
  transcript in `a1`, both in a caller's frame and apart. It is the mirror's step `Model.TM.next`: where the mirror
  returns `v` and `t'`, the slot holds `Ok(v)` and the transcript is `t'`; where it fails, the slot holds an `Err`.
  It writes the slot and the stream offset (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.Next

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ InFrame (regs .x2) (regs .x11) Layouts.Transcript.byteSize ∧
    InFrame (regs .x2) (regs .x10) Layouts.ResultE.byteSize ∧
    Apart (regs .x10) Layouts.ResultE.byteSize (regs .x11) Layouts.Transcript.byteSize

def Post (env : Env) (t : Model.TState) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match Model.TM.next.run t with
  | some (v, t') => ResultEAt m' (regs .x10) (some v) ∧ TranscriptAt env m' (regs .x11) t'
  | none => ResultEAt m' (regs .x10) none

/-- What it writes besides its stack: the result's slot and the transcript's stream offset. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.ResultE.byteSize b ∨
    b = regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset

/-- **The contract of `Transcript::next`**, function `i` of `p` with `need` bytes of stack (it has no frame and
    calls nothing), for every transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post env t) Out

end Rv64mc.Spec.Transcript.Next
