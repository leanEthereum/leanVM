/-
  Rv64mc.Spec.Transcript.AbsorbNonce

  The contract of `Sponge::absorb_nonce(&mut self, nonce: E) -> u64`: the sponge at `a0`, in a caller's frame, the
  nonce's limbs in `a1`, `a2`. It is the mirror's `Model.SpongeRust.absorbNonce`: a return means the mirror
  succeeded (it panics otherwise), the proof of work in `a0` and the sponge the mirror's (stated with
  `Option.getD`). It writes the sponge (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.AbsorbNonce

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (r : Model.SpongeRust) (n : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeAt m (regs .x10) r ∧ InFrame (regs .x2) (regs .x10) Layouts.Sponge.byteSize ∧
    regs .x11 = (Model.limbs n).1 ∧ regs .x12 = (Model.limbs n).2

def Post (r : Model.SpongeRust) (n : E) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (m' : MachineState) : Prop :=
  (r.absorbNonce n).isSome ∧ r' .x10 = ((r.absorbNonce n).getD (0, r)).1 ∧
    SpongeAt m' (regs .x10) ((r.absorbNonce n).getD (0, r)).2

/-- What it writes besides its stack: the sponge. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Sponge.byteSize b

/-- **The contract of `Sponge::absorb_nonce`**, function `i` of `p` with `need` bytes of stack (its frame is 16
    bytes; it calls `absorb` and `duplex`), for every sponge and nonce. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r n, Holds env p i need (Pre r n) (Post r n) Out

end Rv64mc.Spec.Transcript.AbsorbNonce
