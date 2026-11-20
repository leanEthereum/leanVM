/-
  Rv64mc.Spec.Transcript.Sample

  The contract of `Sponge::sample(&mut self) -> E`: the sponge at `a0`, in a caller's frame; it returns the
  mirror's `Model.SpongeRust.sample` challenge (its limbs in `a0`, `a1`) and leaves the mirror's sponge: the ground
  challenge taken, or a permutation and its first two lanes. It writes the sponge (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.Sample

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (r : Model.SpongeRust) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeAt m (regs .x10) r ∧ InFrame (regs .x2) (regs .x10) Layouts.Sponge.byteSize

def Post (r : Model.SpongeRust) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  r' .x10 = (Model.limbs r.sample.1).1 ∧ r' .x11 = (Model.limbs r.sample.1).2 ∧
    SpongeAt m' (regs .x10) r.sample.2

/-- What it writes besides its stack: the sponge. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Sponge.byteSize b

/-- **The contract of `Sponge::sample`**, function `i` of `p` with `need` bytes of stack (its frame is 16 bytes;
    it calls `duplex`), for every sponge. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r, Holds env p i need (Pre r) (Post r) Out

end Rv64mc.Spec.Transcript.Sample
