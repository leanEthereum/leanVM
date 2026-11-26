/-
  Rv64mc.Spec.Transcript.SumcheckRoundPoly

  The contract of `Transcript::sumcheck_round_poly(&mut self, count: usize, claim: E, eq_factor: Option<E>)
  -> Result<Vec<E>, VerifierError>`: the result's slot (`sret`) in `a0`, the transcript in `a1` (as
  `next_scalar`'s), the count in `a2`, the claim's limbs in `a3`, `a4`, and the `Option<E>` by reference in `a5`. It
  is the mirror's `Model.TM.sumcheckRoundPoly`: where the mirror returns the round polynomial and `t'`, the slot holds
  `Ok` of a fresh `Vec` of it and the transcript is `t'`; where it fails, the slot holds `Err`. It writes the slot,
  the sponge and the stream offset (`NextScalar.Out`).
-/

import Rv64mc.Spec.Transcript.NextScalar
import Rv64mc.Spec.Multilinear.Basic

namespace Rv64mc.Spec.Transcript.SumcheckRoundPoly

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (t : Model.TState) (claim : E) (eq : Option E) (regs : Reg → Word) (m : MachineState) :
    Prop :=
  TranscriptAt env m (regs .x11) t ∧ NextScalar.SlotArgs env Layouts.ResultVecE.byteSize regs m ∧
    regs .x13 = (Model.limbs claim).1 ∧ regs .x14 = (Model.limbs claim).2 ∧ OptionEAt m (regs .x15) eq ∧
    Safe env m (regs .x2) (regs .x15) Layouts.OptionE.byteSize ∧
    (regs .x15).toNat + Layouts.OptionE.byteSize < 2 ^ 64

def Post (env : Env) (t : Model.TState) (claim : E) (eq : Option E) (regs : Reg → Word) (m : MachineState)
    (_r' : Reg → Word) (m' : MachineState) : Prop :=
  match (Model.TM.sumcheckRoundPoly (regs .x12).toNat claim eq).run t with
  | some (poly, t') => Multilinear.FreshVecE env m m' (regs .x10) poly ∧ TranscriptAt env m' (regs .x11) t'
  | none => m'.getMem (regs .x10 + BitVec.ofNat 64 Layouts.ResultVecE.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultVecE.Err.tag

/-- **The contract of `Transcript::sumcheck_round_poly`**, function `i` of `p` with `need` bytes of stack (its frame
    is 176 bytes), for every transcript state, claim and equality factor. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t claim eq, Holds env p i need (Pre env t claim eq) (Post env t claim eq)
    (NextScalar.Out Layouts.ResultVecE.byteSize)

end Rv64mc.Spec.Transcript.SumcheckRoundPoly
