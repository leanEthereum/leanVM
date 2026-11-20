/-
  Rv64mc.Spec.Transcript.Absorb

  The contract of `Sponge::absorb(&mut self, value: E, tag: u64)`: the sponge at `a0`, in a caller's frame, the
  value's limbs in `a1`, `a2` and the tag in `a3`. It is the mirror's `Model.SpongeRust.absorb`: where that is
  `none` (a ground challenge waits) the Rust panics, so a return means the mirror succeeded, and the sponge is the
  mirror's. It writes the sponge (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.Absorb

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (r : Model.SpongeRust) (v : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeAt m (regs .x10) r ∧ InFrame (regs .x2) (regs .x10) Layouts.Sponge.byteSize ∧
    regs .x11 = (Model.limbs v).1 ∧ regs .x12 = (Model.limbs v).2

def Post (r : Model.SpongeRust) (v : E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ∃ r', r.absorb v (regs .x13) = some r' ∧ SpongeAt m' (regs .x10) r'

/-- What it writes besides its stack: the sponge. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Sponge.byteSize b

/-- **The contract of `Sponge::absorb`**, function `i` of `p` with `need` bytes of stack (its frame is 48 bytes;
    it calls `duplex` and, on a ground challenge or a count past four, the panics), for every sponge and value. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r v, Holds env p i need (Pre r v) (Post r v) Out

end Rv64mc.Spec.Transcript.Absorb
