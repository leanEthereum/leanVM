/-
  Rv64mc.Spec.Transcript.Duplex

  The contract of `Sponge::duplex(&mut self)`: the sponge at `a0`, in a caller's frame; it becomes the mirror's
  `Model.SpongeRust.duplex`: the rate zeroed, the waiting scalars' lanes over it, permuted, none waiting. It writes the
  sponge (`Out`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Transcript.Duplex

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (r : Model.SpongeRust) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeAt m (regs .x10) r ∧ InFrame (regs .x2) (regs .x10) Layouts.Sponge.byteSize

def Post (r : Model.SpongeRust) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  SpongeAt m' (regs .x10) r.duplex

/-- What it writes besides its stack: the sponge. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Sponge.byteSize b

/-- **The contract of `Sponge::duplex`**, function `i` of `p` with `need` bytes of stack (its frame is 224 bytes;
    it calls `memcpy`, `memset`, `keccak_f` and, on a count past four, `slice_index_fail`), for every sponge. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r, Holds env p i need (Pre r) (Post r) Out

end Rv64mc.Spec.Transcript.Duplex
