/-
  Rv64mc.Spec.Transcript.Sumcheck

  The contract of `verifier::transcript::sumcheck(transcript, claim: E, count: usize, equalities: &[Option<E>])
  -> Result<(Vec<E>, E), VerifierError>`: the result's slot (`sret`) in `a0`, the transcript in `a1` (as
  `next_scalar`'s), the claim's limbs in `a2`, `a3`, the count in `a4`, the equalities as a pointer and a length in
  `a5`, `a6` (each an `Option<E>`, `Layouts.OptionE`). It is the mirror's `Model.TM.sumcheck`: where the mirror
  returns the point and the final claim and `t'`, the slot holds `Ok` of a fresh `Vec` of the point and the claim's
  limbs (`Layouts.VecEE`) and the transcript is `t'`; where it fails, the slot holds `Err`
  (`Layouts.ResultVecEE`'s niche). It writes the slot, the sponge and the stream offset (`NextScalar.Out`).
-/

import Rv64mc.Spec.Transcript.NextScalar
import Rv64mc.Spec.Multilinear.Basic

namespace Rv64mc.Spec.Transcript.Sumcheck

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The `Option<E>`s `es` from `a`, laid end to end. -/
def OptionsAt (m : MachineState) (a : Word) (es : List (Option E)) : Prop :=
  a.toNat + Layouts.OptionE.byteSize * es.length < 2 ^ 64 ∧ ArrayAt Layouts.OptionE.byteSize OptionEAt m a es

def Pre (env : Env) (t : Model.TState) (claim : E) (eqs : List (Option E)) (regs : Reg → Word)
    (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ NextScalar.SlotArgs env Layouts.ResultVecEE.byteSize regs m ∧
    regs .x12 = (Model.limbs claim).1 ∧ regs .x13 = (Model.limbs claim).2 ∧
    SliceArgs OptionsAt m (regs .x15) (regs .x16) eqs ∧
    env.Live m (regs .x15) (Layouts.OptionE.byteSize * eqs.length)

def Post (env : Env) (t : Model.TState) (claim : E) (eqs : List (Option E)) (regs : Reg → Word)
    (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  match (Model.TM.sumcheck claim (regs .x14).toNat eqs).run t with
  | some ((point, c), t') =>
    Multilinear.FreshVecE env m m' (regs .x10 + BitVec.ofNat 64 Layouts.VecEE.f0) point ∧
      EAt m' (regs .x10 + BitVec.ofNat 64 Layouts.VecEE.f1) (Model.limbs c) ∧ TranscriptAt env m' (regs .x11) t'
  | none => m'.getMem (regs .x10 + BitVec.ofNat 64 Layouts.ResultVecEE.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultVecEE.Err.tag

/-- **The contract of `sumcheck`**, function `i` of `p` with `need` bytes of stack (its frame is 160 bytes), for
    every transcript state, claim and list of equality factors. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t claim eqs, Holds env p i need (Pre env t claim eqs) (Post env t claim eqs)
    (NextScalar.Out Layouts.ResultVecEE.byteSize)

end Rv64mc.Spec.Transcript.Sumcheck
