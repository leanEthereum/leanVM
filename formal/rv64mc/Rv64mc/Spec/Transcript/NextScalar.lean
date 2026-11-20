/-
  Rv64mc.Spec.Transcript.NextScalar

  The contract of `Transcript::next_scalar(&mut self) -> Result<E, VerifierError>`: the result's slot (`sret`) in
  `a0`, the transcript in `a1`, as `Transcript::next`'s. It is the mirror's step `Model.TM.nextScalar`: the next
  scalar of the stream, observed. It writes the slot and the transcript (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.NextScalar

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- A result slot of `size` bytes at `a0`, beside the transcript at `a1`: both in a caller's frame, the slot apart
    from the transcript and its `Proof`, which is safe from the call. -/
def SlotArgs (env : Env) (size : Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  InFrame (regs .x2) (regs .x11) Layouts.Transcript.byteSize ∧ InFrame (regs .x2) (regs .x10) size ∧
    ProofSafe env m (regs .x2) (regs .x11) ∧
    Apart (regs .x10) size (regs .x11) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) size (proofAddr m (regs .x11)) Layouts.Proof.byteSize

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ SlotArgs env Layouts.ResultE.byteSize regs m

def Post (env : Env) (t : Model.TState) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match Model.TM.nextScalar.run t with
  | some (v, t') => ResultEAt m' (regs .x10) (some v) ∧ TranscriptAt env m' (regs .x11) t'
  | none => ResultEAt m' (regs .x10) none

/-- What a transcript method with a result slot writes besides its stack: the slot and the transcript. -/
def Out (size : Nat) (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) size b ∨ InRange (regs .x11) Layouts.Transcript.byteSize b

/-- **The contract of `Transcript::next_scalar`**, function `i` of `p` with `need` bytes of stack (its frame is
    64 bytes; it calls `next` and `Sponge::absorb`), for every transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post env t) (Out Layouts.ResultE.byteSize)

end Rv64mc.Spec.Transcript.NextScalar
