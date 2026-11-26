/-
  Rv64mc.Spec.Transcript.GrindCheck

  The contract of `Transcript::grind_check(&mut self, bits: u32) -> Result<(), VerifierError>`: the transcript in
  `a0`, in a caller's frame (its `Proof` safe from the call), the bits in `a1`; the result's tag in `a0`
  (`Layouts.ResultUnit`: `Ok` is the niche value). It returns `Ok` exactly where the mirror's step
  `Model.TM.grindCheck` succeeds, and then the transcript is the mirror's. It writes the sponge and the stream offset (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.GrindCheck

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x10) t ∧ InFrame (regs .x2) (regs .x10) Layouts.Transcript.byteSize ∧
    ProofSafe env m (regs .x2) (regs .x10) ∧ (regs .x11).toNat < 2 ^ 32

def Post (env : Env) (t : Model.TState) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match (Model.TM.grindCheck (regs .x11).toNat).run t with
  | some ((), t') => r' .x10 = BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag ∧ TranscriptAt env m' (regs .x10) t'
  | none => r' .x10 ≠ BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag

/-- What it writes besides its stack: the sponge and the stream offset. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.Sponge.byteSize b ∨ b = regs .x10 + BitVec.ofNat 64 Layouts.Transcript.stream_offset

/-- **The contract of `Transcript::grind_check`**, function `i` of `p` with `need` bytes of stack (its frame is 64
    bytes; it calls `next` and `Sponge::absorb_nonce`), for every transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (Pre env t) (Post env t) Out

end Rv64mc.Spec.Transcript.GrindCheck
