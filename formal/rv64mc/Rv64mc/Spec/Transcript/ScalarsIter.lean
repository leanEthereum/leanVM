/-
  Rv64mc.Spec.Transcript.ScalarsIter

  The contract of `next_scalars`' iterator, `<GenericShunt<Map<Range<usize>, next_scalars::{closure}>,
  Result<!, VerifierError>> as Iterator>::next`: the result's slot (`Option<E>`, `sret`) in `a0`, the shunt in `a1`
  (the transcript's address, the range's start and end, the residual's address, `shunt*`). It is one step of the
  mirror's `Model.TM.nextScalars`: with the range not exhausted it advances the start and reads a scalar
  (`Model.TM.nextScalar`), returning `Some` of it with the transcript the mirror's and the residual kept, or `None`
  with the error in the residual (its first word not `Ok`'s niche); with the range exhausted it returns `None` and
  keeps the transcript and the residual. It writes the slot, the start, the transcript's sponge and stream offset,
  and the residual (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.ScalarsIter

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The shunt's fields: the transcript's address, the range, the residual's address. -/
def shuntT (m : MachineState) (a : Word) : Word := m.getMem a
def shuntStart (m : MachineState) (a : Word) : Word := m.getMem (a + 8#64)
def shuntEnd (m : MachineState) (a : Word) : Word := m.getMem (a + 16#64)
def shuntRes (m : MachineState) (a : Word) : Word := m.getMem (a + 24#64)

/-- The objects of a call: the slot (`24` bytes), the shunt (`32`), the residual (`16`), each in a caller's frame
    and apart from each other and from the transcript and its `Proof`; the transcript in a caller's frame, its
    `Proof` safe from the call. -/
def Objects (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InFrame (regs .x2) (shuntT m (regs .x11)) Layouts.Transcript.byteSize ∧
    ProofSafe env m (regs .x2) (shuntT m (regs .x11)) ∧
    InFrame (regs .x2) (regs .x10) Layouts.OptionE.byteSize ∧ InFrame (regs .x2) (regs .x11) 32 ∧
    InFrame (regs .x2) (shuntRes m (regs .x11)) 16 ∧
    Apart (regs .x10) Layouts.OptionE.byteSize (shuntT m (regs .x11)) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) Layouts.OptionE.byteSize (proofAddr m (shuntT m (regs .x11))) Layouts.Proof.byteSize ∧
    Apart (regs .x11) 32 (shuntT m (regs .x11)) Layouts.Transcript.byteSize ∧
    Apart (regs .x11) 32 (proofAddr m (shuntT m (regs .x11))) Layouts.Proof.byteSize ∧
    Apart (shuntRes m (regs .x11)) 16 (shuntT m (regs .x11)) Layouts.Transcript.byteSize ∧
    Apart (shuntRes m (regs .x11)) 16 (proofAddr m (shuntT m (regs .x11))) Layouts.Proof.byteSize ∧
    Apart (regs .x10) Layouts.OptionE.byteSize (regs .x11) 32 ∧
    Apart (shuntRes m (regs .x11)) 16 (regs .x10) Layouts.OptionE.byteSize ∧
    Apart (shuntRes m (regs .x11)) 16 (regs .x11) 32

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (shuntT m (regs .x11)) t ∧ Objects env regs m

/-- The step on a range not exhausted: the start advanced, the scalar read as the mirror reads it. -/
def Step (env : Env) (t : Model.TState) (regs : Reg → Word) (m m' : MachineState) : Prop :=
  match Model.TM.nextScalar.run t with
  | some (v, t') => OptionEAt m' (regs .x10) (some v) ∧ TranscriptAt env m' (shuntT m (regs .x11)) t' ∧
      m'.getMem (shuntRes m (regs .x11)) = m.getMem (shuntRes m (regs .x11))
  | none => OptionEAt m' (regs .x10) none ∧
      m'.getMem (shuntRes m (regs .x11)) ≠ BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag

def Post (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  (shuntStart m (regs .x11) < shuntEnd m (regs .x11) →
    shuntStart m' (regs .x11) = shuntStart m (regs .x11) + 1#64 ∧ Step env t regs m m') ∧
  (shuntEnd m (regs .x11) ≤ shuntStart m (regs .x11) →
    OptionEAt m' (regs .x10) none ∧ TranscriptAt env m' (shuntT m (regs .x11)) t ∧
      m'.getMem (shuntRes m (regs .x11)) = m.getMem (shuntRes m (regs .x11)))

/-- What it writes besides its stack: the slot, the start, the transcript's sponge and stream offset, and the
    residual. -/
def Out (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.OptionE.byteSize b ∨ b = regs .x11 + 8#64 ∨
    InRange (shuntT m (regs .x11)) Layouts.Sponge.byteSize b ∨
    b = shuntT m (regs .x11) + BitVec.ofNat 64 Layouts.Transcript.stream_offset ∨
    InRange (shuntRes m (regs .x11)) 16 b

/-- **The contract of `next_scalars`' iterator**, function `i` of `p` with `need` bytes of stack (its frame is 48
    bytes; it calls `next_scalar`), for every transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post env t) Out

end Rv64mc.Spec.Transcript.ScalarsIter
