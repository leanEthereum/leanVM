/-
  Rv64mc.Spec.Transcript.Samples

  The contract of `Transcript::samples(&mut self, count: usize) -> Vec<E>`: the result's slot (`sret`) in `a0`, the
  transcript in `a1` (as `next_scalar`'s), the count in `a2`. The slot holds a fresh `Vec` of the mirror's
  `Model.TM.samples count` challenges, and the transcript is the mirror's (which always succeeds). It writes the
  slot and the transcript (`Out`).
-/

import Rv64mc.Spec.Transcript.NextScalar
import Rv64mc.Spec.Multilinear.Basic

namespace Rv64mc.Spec.Transcript.Samples

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ NextScalar.SlotArgs env Layouts.Vec.byteSize regs m

def Post (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ∀ xs t', (Model.TM.samples (regs .x12).toNat).run t = some (xs, t') →
    Multilinear.FreshVecE env m m' (regs .x10) xs ∧ TranscriptAt env m' (regs .x11) t'

/-- **The contract of `Transcript::samples`**, function `i` of `p` with `need` bytes of stack (its frame is 80
    bytes; it calls `Sponge::sample`, `alloc`, `Vec::reserve` and `handle_error`), for every transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post env t) (NextScalar.Out Layouts.Vec.byteSize)

end Rv64mc.Spec.Transcript.Samples
