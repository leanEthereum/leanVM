/-
  Rv64mc.Spec.Transcript.NextScalars

  The contract of `Transcript::next_scalars(&mut self, count: usize) -> Result<Vec<E>, VerifierError>`: the
  result's slot (`sret`) in `a0`, the transcript in `a1` (as `next_scalar`'s), the count in `a2`. It is the mirror's
  `Model.TM.nextScalars count`: where the mirror returns `xs` and `t'`, the slot holds `Ok` of a fresh `Vec` of `xs`
  and the transcript is `t'`; where it fails, the slot holds `Err` (`Layouts.ResultVecE`'s niche tag). It writes the
  slot and the transcript (`Out`).
-/

import Rv64mc.Spec.Transcript.NextScalar
import Rv64mc.Spec.Multilinear.Basic

namespace Rv64mc.Spec.Transcript.NextScalars

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ NextScalar.SlotArgs env Layouts.ResultVecE.byteSize regs m

def Post (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match (Model.TM.nextScalars (regs .x12).toNat).run t with
  | some (xs, t') => Multilinear.FreshVecE env m m' (regs .x10) xs ∧ TranscriptAt env m' (regs .x11) t'
  | none => m'.getMem (regs .x10 + BitVec.ofNat 64 Layouts.ResultVecE.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultVecE.Err.tag

/-- **The contract of `Transcript::next_scalars`**, function `i` of `p` with `need` bytes of stack (its frame is
    192 bytes; it calls the iterator's `next`, `alloc`, `Vec::reserve` and `handle_error`), for every transcript
    state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post env t) (NextScalar.Out Layouts.ResultVecE.byteSize)

end Rv64mc.Spec.Transcript.NextScalars
